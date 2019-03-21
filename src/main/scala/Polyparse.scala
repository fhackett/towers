package polyparse

import scala.quoted._
//import scala.quoted.Toolbox.Default._


sealed trait Grammar[AT:Type,T:Type,ET:Type] {
  val tType = implicitly[Type[T]]
  val eType = implicitly[Type[ET]]
  val aType = implicitly[Type[AT]]
  type t = T
  type at = AT
}

private case class Terminal[T:Type:Liftable](val v : T) extends Grammar[Unit,T,T] {
  val liftable = implicitly[Liftable[T]]
}
private case class ArgumentTerminal[T:Type]() extends Grammar[T,T,T]
private case class ArgToVal[T:Type]() extends Grammar[T,T,Any]
private case class ReadPos() extends Grammar[Unit,Int,Any]
private case class Call[AT1:Type,AT2:Type,T:Type,ET:Type](val arg : Grammar[AT1,AT2,ET], val fn : Grammar[AT2,T,ET]) extends Grammar[AT1,T,ET]
private case class Sequence[AT:Type,LT:Type,RT:Type,ET:Type](val left : Grammar[AT,LT,ET], val right : Grammar[AT,RT,ET]) extends Grammar[AT,(LT,RT),ET]
private case class Check[AT:Type,ET:Type](val g : Grammar[AT,Any,ET]) extends Grammar[AT,Unit,ET]
private case class Disjunction[AT:Type,T:Type,ET:Type](val left : Grammar[AT,T,ET], val right : Grammar[AT,T,ET]) extends Grammar[AT,T,ET]
private case class Condition[AT:Type,T:Type,ET:Type](val g : Grammar[AT,T,ET], val cond : Expr[T] => Expr[Boolean]) extends Grammar[AT,T,ET]
private case class MapArg[AT1:Type,AT2,T:Type,ET:Type](val to : Grammar[AT2,T,ET], val fn : Expr[AT1] => Expr[AT2]) extends Grammar[AT1,T,ET]
private case class MapVal[AT:Type,T1,T2:Type,ET:Type](val from : Grammar[AT,T1,ET], val fn : Expr[T1] => Expr[T2]) extends Grammar[AT,T2,ET]
private class Recursion[AT:Type,T:Type,ET:Type](_g : =>Grammar[AT,T,ET]) extends Grammar[AT,T,ET] {
  lazy val g = _g
}

sealed trait BlockIR[In:Type,Out:Type] {
  val tIn = implicitly[Type[In]]
  val tOut = implicitly[Type[Out]]
}

trait BlockContext[In:Type,-Out:Type] {
  def fail : Expr[Unit]
  def arg : Expr[In]
  def succeed(v : Expr[Out]) : Expr[Unit]
}

case class BranchIR[In:Type,Out:Type](val condition : BlockContext[In,Out] => Expr[Boolean], val yes : BlockIR[In,Out], val no : BlockIR[In,Out]) extends BlockIR[In,Out]
case class PreserveArgIR[In:Type,Out:Type](val g : BlockIR[In,Out]) extends BlockIR[In,(In,Out)] // produces a tuple of original arg and g's result
case class SeqIR[In:Type,Mid:Type,Out:Type](val from : BlockIR[In,Mid], val to : BlockIR[Mid,Out]) extends BlockIR[In,Out] // makes result of from arg of to
case class CallIR[In:Type,Out:Type](val key : AnyRef) extends BlockIR[In,Out]
case class RecoverIR[In:Type,Out:Type](val first : BlockIR[In,Out], val second : BlockIR[In,Out]) extends BlockIR[In,Out]
case class SimpleIR[In:Type,Out:Type](val fn : BlockContext[In,Out] => Expr[Unit]) extends BlockIR[In,Out]

sealed trait BlockIR2[In:Type] {
  val tIn = implicitly[Type[In]]
  type in = In
}

case class BranchIR2[In:Type](val condition : BlockContext[In,Any] => Expr[Boolean], val yes : BlockIR2[In], val no : BlockIR2[In]) extends BlockIR2[In]
case class BeforeIR2[In:Type,In2:Type](val map : BlockContext[In,In2] => Expr[Unit], val next : BlockIR2[In2]) extends BlockIR2[In]
case class JumpIR2[In:Type](val key : AnyRef, val ret : AnyRef) extends BlockIR2[In]
case class ReturnIR2[In:Type]() extends BlockIR2[In]

trait SequenceContext[ET:Type] {
  type Mark
  def mark : Expr[Mark]
  def restore(m : Expr[Mark]) : Expr[Unit]
  def peek : Expr[ET]
  def isEOF : Expr[Boolean]
  def next : Expr[Unit]
}

trait ControlFlowContext[Result] {
  type Label = Int

  def block(e : Expr[Unit]) : Label = block(_ => e)
  def block(fn : Label=>Expr[Unit]) : Label
  def callReg[T:Type] : Expr[T]
  def retReg[T:Type] : Expr[T]

  def end(v : Expr[Result]) : Expr[Unit]

  def call(label : Label, ret : Label, arg : Expr[Any]) : Expr[Unit]
  def ret(v : Expr[Any]) : Expr[Unit]

  def push(v : Expr[Any]) : Expr[Unit]
  def pop : Expr[Any]
}

trait MakeSequenceContext[Seq[_]] {
  def makeCtx[ET:Type,Result:Type](fn : SequenceContext[ET] => Expr[Result]) : Expr[Seq[ET] => Result]
}

case class BlockCompiler[ET:Type,Result](seqCtx : SequenceContext[ET]) {
  def speculateReachable[AT:Type,T:Type](g : Grammar[AT,T,ET], arg : Expr[AT]) : Expr[Boolean] = g match {
    case t@Terminal(v) => {
      implicit val _ = t.liftable
      '{ !${seqCtx.isEOF} && ${seqCtx.peek} == ${v.toExpr}}
    }
    case Disjunction(l,r) => '{ ${speculateReachable(l, arg)} || ${speculateReachable(r, arg)} }
    case Sequence(l,r) => {
      implicit val _ = l.tType
      speculateReachable(l, arg)
    }
    case ArgumentTerminal() => '{ !${seqCtx.isEOF} && ${seqCtx.peek} == $arg }
    case Call(l,_) => {
      implicit val _ = l.tType
      speculateReachable(l, arg)
    }
    case Condition(gg,cond) => speculateReachable(gg, arg)
    case MapArg(to,fn) => {
      implicit val _ = to.aType
      speculateReachable(to, fn(arg))
    }
    case MapVal(gg,_) => {
      implicit val _ = gg.tType
      speculateReachable(gg, arg)
    }
    case Check(gg) => speculateReachable(gg, arg)
    case r : Recursion[AT,T,ET] => speculateReachable(r.g, arg) // speculate past calls to avoid redundantly calling parser we know will fail
                                                                // note: this only works if the parser terminates :) ... maybe catch obvious
                                                                // non-termination later
    case _ => ???
  }
  def computeBlocks[AT:Type,T:Type](g : Grammar[AT,T,ET]) : Seq[(AnyRef, BlockIR[_,_])] = g match {
    case t@Terminal(v) => Seq(
      (t, SimpleIR[AT,T](ctx => {
        implicit val _ = t.liftable
        '{
          if !${seqCtx.isEOF} && ${seqCtx.peek} == ${v.toExpr}
          then ${ctx.succeed(v.toExpr)}
          else ${ctx.fail}
        }
      }))
    )
    case Disjunction(l, r) => Seq(
      (g, BranchIR[AT,T](
        condition=ctx => speculateReachable(l, ctx.arg),
        yes=CallIR[AT,T](l),
        no=CallIR[AT,T](r),
      ))
    ) ++ computeBlocks(l) ++ computeBlocks(r)
    case Sequence(l, r) => {
      implicit val _ = l.tType
      implicit val _1 = r.tType
      type LT = l.t
      type RT = r.t
      Seq(
        (g, SeqIR(
          PreserveArgIR(CallIR[AT,LT](l)),
          SeqIR(
            PreserveArgIR(SeqIR(
              SimpleIR[(AT,LT),AT](ctx => ctx.succeed('{${ctx.arg} match { case (in,_) => in }})),
              CallIR[AT,RT](r)
            )),
            SimpleIR[((AT,LT),RT),(LT,RT)](ctx => ctx.succeed('{${ctx.arg} match { case ((_,res1),res2) => (res1,res2) }}))
          )
        )),
      ) ++ computeBlocks(l) ++ computeBlocks(r)
    }
    case Call(arg, fn) => {
      implicit val _ = arg.tType
      type AAT = arg.t
      Seq(
        (g, SeqIR(CallIR[AT,AAT](arg), CallIR[AAT,T](fn)))
      ) ++ computeBlocks(arg) ++ computeBlocks(fn)
    }
    case ArgumentTerminal() => Seq(
      (g, SimpleIR(ctx => '{
        if !${seqCtx.isEOF} && ${seqCtx.peek} == ${ctx.arg}
        then ${ctx.succeed(ctx.arg)}
        else ${ctx.fail}
      }))
    )
    case Condition(gg, cond) => Seq(
      (g, SeqIR(CallIR[AT,T](gg), SimpleIR[T,T](ctx => '{
        if ${cond(ctx.arg)}
        then ${ctx.succeed(ctx.arg)}
        else ${ctx.fail}
      })))
    ) ++ computeBlocks(gg)
    case MapArg(to,fn) => {
      implicit val _ = to.aType
      type TAT = to.at
      Seq(
        (g, SeqIR(SimpleIR[AT,TAT](ctx => ctx.succeed(fn(ctx.arg))), CallIR[TAT,T](to)))
      ) ++ computeBlocks(to)
    }
    case MapVal(from,fn) => {
      implicit val _ = from.tType
      type FT = from.t
      Seq(
        (g, SeqIR(CallIR[AT,FT](from), SimpleIR[FT,T](ctx => ctx.succeed(fn(ctx.arg)))))
      ) ++ computeBlocks(from)
    }
    case r : Recursion[AT,T,ET] => Seq((g, CallIR[AT,T](r.g)))
    case _ => ???
  }
}

object PolyParse {

  private def maybeRecurse[AT:Type,T:Type,ET:Type](g : =>Grammar[AT,T,ET]) : Grammar[AT,T,ET] = if g == null then new Recursion(g) else g


  implicit class MaybeRecursion[AT:Type,T:Type,ET:Type](g : =>Grammar[AT,T,ET]) {
    def <|>(other : =>Grammar[AT,T,ET]) : Grammar[AT,T,ET] = Disjunction(maybeRecurse(g), maybeRecurse(other))
    def ++[Other:Type](other : =>Grammar[AT,Other,ET]) : Grammar[AT,(T,Other),ET] = Sequence(maybeRecurse(g), maybeRecurse(other))
    //def map[T2:Type](fn : Expr[T] => Expr[T2]) : Grammar[T2,ET] = Mapping(maybeRecurse(g), fn)
    //def ??(cond : Expr[T] => Expr[Boolean]) : Grammar[T,ET] = Condition(maybeRecurse(g), cond)
  }

  def term[T:Type:Liftable](v : T) : Grammar[Unit,T,T] = Terminal(v)
  def $[T:Type] : Grammar[T,T,T] = ArgumentTerminal()
  def $$[T:Type] : Grammar[T,T,Any] = ArgToVal()

  implicit object MakeListContext extends MakeSequenceContext[List] {
    def makeCtx[ET:Type,Result:Type](fn : SequenceContext[ET] => Expr[Result]) : Expr[List[ET] => Result] = '{(list_ : List[ET]) => {
      var list = list_
      ${fn(new {
        type Mark = List[ET]
        def mark : Expr[Mark] = '{ list }
        def restore(m : Expr[List[ET]]) : Expr[Unit] = '{ list = $m } // replace with Mark once Dotty devs fix
        def peek : Expr[ET] = '{ list.head }
        def isEOF : Expr[Boolean] = '{ list.isEmpty }
        def next : Expr[Unit] = '{ list = list.tail }
      })}
    }}
  }


  def makeControlFlowContext[Result:Type](fn : ControlFlowContext[Result] => Unit) : Expr[Result] = '{
    import collection.mutable.ArrayStack
    val stackPC : ArrayStack[Int] = new ArrayStack
    val stack : ArrayStack[Any] = new ArrayStack
    var pc : Int = 0
    var callReg_ : Any = null
    var retReg_ : Any = null
    var loop = true
    while(loop) {
      ${
        import collection.mutable.ArrayBuffer
        val blocks = new ArrayBuffer[(Int,Expr[Unit])]
        fn(new {
          type Label = Int
          def block(f : Int=>Expr[Unit]) : Int = {
            val label = blocks.length
            blocks += null
            blocks(label) = (label, f(label))
            label
          }
          def callReg[T:Type] : Expr[T] = '{callReg_.asInstanceOf[T]}
          def retReg[T:Type] : Expr[T] = '{retReg_.asInstanceOf[T]}
          def end(v : Expr[Result]) : Expr[Unit] = '{
            retReg_ = $v
            loop = false
          }
          def call(label : Int, ret : Int, a : Expr[Any]) : Expr[Unit] = '{
            pc = ${label.toExpr}
            callReg_ = $a
            stackPC.push(${ret.toExpr})
          }
          def ret(v : Expr[Any]) : Expr[Unit] = '{
            pc = stackPC.pop
            retReg_ = $v
          }
          def push(v : Expr[Any]) : Expr[Unit] = '{
            stack.push($v)
          }
          def pop : Expr[Any] = '{ stack.pop }
        })
        blocks.foldRight[Expr[Unit]]('{ ??? })((pair, rest) => pair match {
          case (i, block) => '{if pc == ${i.toExpr} then $block else $rest}
        })
      }
    }
    retReg_.asInstanceOf[Result]
  }

  def performInlining(blocks : Seq[(AnyRef,BlockIR[_,_])]) : Seq[(AnyRef,BlockIR[_,_])] = blocks // FIXME: actually do it

  def splitBasicBlocks[In:Type,Out:Type](b : BlockIR[In,Out], rest : BlockIR2[Out]) : (BlockIR2[In],Seq[(AnyRef,BlockIR2[_])]) = b match {
    case BranchIR(condition,yes,no) => {
      val (yBlock, yBlocks) = splitBasicBlocks(yes,rest)
      val (nBlock, nBlocks) = splitBasicBlocks(no,rest)
      (BranchIR2[In](condition,yBlock,nBlock), yBlocks ++ nBlocks)
    }
    case SeqIR(left,right) => {
      implicit val _ = left.tOut
      val (rBlock, rBlocks) = splitBasicBlocks(right,rest)
      val (lBlock, lBlocks) = splitBasicBlocks(left, rBlock)
      (lBlock, lBlocks ++ rBlocks)
    }
    case CallIR(key) => {
      (JumpIR2(key,(key,rest)), Seq(((key,rest),rest)))
    }
    case SimpleIR(fn) => {
      (BeforeIR2[In,Out](fn, rest), Seq())
    }
    case _ => ???
  }

  def compile[T:Type,ET:Type,Seq[_]:MakeSequenceContext](g : Grammar[Unit,T,ET])(implicit seqT : Type[Seq[T]]) : Expr[Seq[ET] => Option[T]] = {
    def findRecursions[AT,T,ET](g : Grammar[AT,T,ET]) : Set[Grammar[_,_,_]] = g match {
      case Terminal(_) => Set.empty
      case Sequence(a,b) => findRecursions(a) | findRecursions(b)
      case Disjunction(a,b) => findRecursions(a) | findRecursions(b)
      case r : Recursion[AT,T,ET] => Set(r.g)
      case _ => ???
    }
    val recursions = findRecursions(g)
    println(recursions)

    implicitly[MakeSequenceContext[Seq]].makeCtx(seqCtx => {
      makeControlFlowContext[Option[T]](flowCtx => {
        flowCtx.block(root => {
          val compiler = BlockCompiler(seqCtx)
          val blocks = compiler.computeBlocks(g)
          val inlinedBlocks = performInlining(blocks)
          val basicBlocks = inlinedBlocks.flatMap(block => {
            val (key,b) = block
            implicit val _ = b.tIn
            implicit val _1 = b.tOut
            val root, blocks = splitBasicBlocks(b, ReturnIR2())
            Seq((key,root),blocks)
          })
          println(basicBlocks)
          '{()}
        })
      })
    })
  }

  def main(argv : Array[String]) : Unit = {
    import scala.quoted.Toolbox.Default._
    object vv {
      val v : Grammar[Unit,Int,Int] = term(1) <|> term(2) <|> v 
      val v2 : Grammar[Unit,(Int,Int),Int] = (term(1) ++ term(2)) <|> v2
    }
    println(compile[Int,Int,List](vv.v).show)
  }
}

