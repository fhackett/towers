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
  type in = In
  type out = Out
}

trait BlockContext[In:Type,-Out:Type] {
  def fail : Expr[Unit]
  def arg : Expr[In]
  def succeed(v : Expr[Out]) : Expr[Unit]
}

case class BranchIR[In:Type,Out:Type](val condition : Expr[In] => Expr[Boolean], val yes : BlockIR[In,Out], val no : BlockIR[In,Out]) extends BlockIR[In,Out]
case class PreserveArgIR[In:Type,Out:Type](val g : BlockIR[In,Out]) extends BlockIR[In,(In,Out)] // produces a tuple of original arg and g's result
case class SeqIR[In:Type,Mid:Type,Out:Type](val from : BlockIR[In,Mid], val to : BlockIR[Mid,Out]) extends BlockIR[In,Out] // makes result of from arg of to
case class CallIR[In:Type,Out:Type](val key : AnyRef) extends BlockIR[In,Out]
case class RecoverIR[In:Type,Out:Type](val first : BlockIR[In,Out], val second : BlockIR[In,Out]) extends BlockIR[In,Out]
case class SimpleIR[In:Type,Out:Type](val fn : BlockContext[In,Out] => Expr[Unit]) extends BlockIR[In,Out]

sealed trait BlockIR2[In:Type] {
  val tIn = implicitly[Type[In]]
  type in = In
}

case class BranchIR2[In:Type](val condition : Expr[In] => Expr[Boolean], val yes : BlockIR2[In], val no : BlockIR2[In]) extends BlockIR2[In]
case class BeforeIR2[In:Type,In2:Type](val map : BlockContext[In,In2] => Expr[Unit], val next : BlockIR2[In2]) extends BlockIR2[In]
case class CallIR2[In:Type](val key : AnyRef, val ret : AnyRef) extends BlockIR2[In]
case class JumpIR2[In:Type](val Key : AnyRef) extends BlockIR2[In]
case class ReturnIR2[In:Type]() extends BlockIR2[In]
case class PushArgIR2[In:Type](val b : BlockIR2[In]) extends BlockIR2[In]
case class PopArgIR2[In:Type,Arg:Type](val b : BlockIR2[(Arg,In)]) extends BlockIR2[In] {
  val tArg = implicitly[Type[Arg]]
  type arg = Arg
}
case class PushRecoverIR2[In:Type](val failKey : AnyRef, val b : BlockIR2[In]) extends BlockIR2[In]

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
        condition=arg => speculateReachable(l, arg),
        yes=CallIR[AT,T](l),
        no=CallIR[AT,T](r),
      ))
    ) ++ computeBlocks(l) ++ computeBlocks(r)
    case Sequence(l, r) => {
      // this bizarre construct is a workaround to lampepfl/dotty#6142
      def fn[LT:Type,RT:Type](ll : Grammar[AT,LT,ET], rr : Grammar[AT,RT,ET]) = {
        val l = ll
        val r = rr
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
      fn(l,r)(l.tType,r.tType)
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

case class BlockInliner(blockMap : Map[AnyRef,BlockIR[_,_]], reachable : Set[AnyRef], inboundCounts : Map[AnyRef,Int]) {
  def inliningTransform[In,Out](b : BlockIR[In,Out]) : BlockIR[In,Out] = b match {
    case CallIR(key) => {
      if (inboundCounts(key) == 1)
      then blockMap(key).asInstanceOf[BlockIR[In,Out]]
      else b
    }
    case RecoverIR(left,right) =>
      RecoverIR(inliningTransform(left), inliningTransform(right))(left.tIn,left.tOut)
    case BranchIR(condition,left,right) =>
      BranchIR(condition, inliningTransform(left), inliningTransform(right))(left.tIn,left.tOut)
    case SeqIR(left,right) =>
      SeqIR(inliningTransform(left), inliningTransform(right))(left.tIn,left.tOut,right.tOut)
    case SimpleIR(_) => b
    case PreserveArgIR(b) => PreserveArgIR(inliningTransform(b))(b.tIn,b.tOut)
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

  def summingCombine(a : Map[AnyRef,Int], b : Map[AnyRef,Int]) : Map[AnyRef,Int] =
    a.foldLeft(b)((acc, tpl) => {
      val (k,v) = tpl
      if acc.contains(k) then acc.updated(k, acc(k)+v) else acc.updated(k,v)
    })

  def calculateInboundCounts(b : BlockIR[_,_], map : Map[AnyRef,BlockIR[_,_]], visited : Set[AnyRef]) : (Map[AnyRef,Int],Set[AnyRef]) =
    b match {
      case CallIR(key) =>
        if visited.contains(key)
        then (Map(key -> 1), visited)
        else {
          val (counts, vis) = calculateInboundCounts(map(key), map, visited+key)
          (summingCombine(Map(key -> 1), counts), vis)
        }
      case RecoverIR(left,right) => {
        val (counts1, vis1) = calculateInboundCounts(left, map, visited)
        val (counts2, vis2) = calculateInboundCounts(right, map, vis1)
        (summingCombine(counts1,counts2), vis2)
      }
      case BranchIR(_,left,right) => {
        val (counts1, vis1) = calculateInboundCounts(left, map, visited)
        val (counts2, vis2) = calculateInboundCounts(right, map, vis1)
        (summingCombine(counts1,counts2), vis2)
      }
      case SeqIR(left,right) => {
        val (counts1, vis1) = calculateInboundCounts(left, map, visited)
        val (counts2, vis2) = calculateInboundCounts(right, map, vis1)
        (summingCombine(counts1,counts2), vis2)
      }
      case SimpleIR(_) => (Map(), visited)
      case PreserveArgIR(b) => calculateInboundCounts(b, map, visited)
    }

  def performInlining(blocks : Seq[(AnyRef,BlockIR[_,_])]) : Seq[(AnyRef,BlockIR[_,_])] = {
    val blockMap = blocks.toMap
    val (rootKey, root) = blocks.head
    val (inboundCounts_, reachableSet) = calculateInboundCounts(root, blockMap, Set(rootKey))
    val inboundCounts = summingCombine(Map(rootKey -> 1), inboundCounts_)
    val inliner : BlockInliner = BlockInliner(blockMap, reachableSet, inboundCounts)
    val inlinedBlocks = blocks.map(kv => kv match {
      case (key, b) => (key, inliner.inliningTransform(b))
    })
    val (_, root2) = inlinedBlocks.head
    val (_, reachableSet2) = calculateInboundCounts(root2, blockMap, Set(rootKey))
    val prunedBlocks = inlinedBlocks.filter(kv => kv match {
      case (key, _) => reachableSet2(key)
    })
    prunedBlocks
  }

  def containsJumps[In,Out](b : BlockIR[In,Out]) : Boolean = b match {
    case BranchIR(condition, yes, no) => containsJumps(yes) || containsJumps(no)
    case SeqIR(left,right) => containsJumps(left) || containsJumps(right)
    case CallIR(_) => true
    case SimpleIR(_) => false
    case PreserveArgIR(bb) => containsJumps(bb)
    case RecoverIR(yes,no) => true
  }

  def compileJumplessBlock[In:Type,Out:Type](b : BlockIR[In,Out], ctx : BlockContext[In,Out]) : Expr[Unit] = b match {
    case BranchIR(condition, yes, no) => '{
      var out : Out = null.asInstanceOf[Out]
      var success = true
      ${
        // avoid pasting the "rest" into both branches of the conditional
        val nctx : BlockContext[In,Out] = new {
          def arg = ctx.arg
          def fail = '{ success = false }
          def succeed(v : Expr[Out]) = '{ out = ${v} }
        }
        '{
          if ${condition(ctx.arg)}
          then ${compileJumplessBlock(yes,nctx)}
          else ${compileJumplessBlock(no,nctx)}
          if success
          then ${ctx.succeed('{out})}
          else ${ctx.fail}
        }
      }
    }
    case SeqIR(left,right) => {
      implicit val e1 = right.tIn
      compileJumplessBlock(left, new {
        def arg = ctx.arg
        def fail = ctx.fail
        def succeed(v : Expr[right.in]) = compileJumplessBlock(right, new {
          def arg = v
          def fail = ctx.fail
          def succeed(v : Expr[Out]) = ctx.succeed(v)
        })
      })
    }
    case CallIR(_) => ??? // this is a jumpless block, so should be unreachable
    case SimpleIR(fn) => fn(ctx)
    case PreserveArgIR(bb) => {
      implicit val e1 = bb.tOut
      '{
        val holdArg = ${ctx.arg}
        ${compileJumplessBlock(bb, new BlockContext[In,bb.out]() {
          def arg = '{ holdArg }
          def fail = ctx.fail
          def succeed(v : Expr[bb.out]) = ctx.succeed('{ (holdArg, ${v}) })
        })}
      }
    }
    case RecoverIR(_,_) => ??? // can't inline the non-local recovery part
  }

  def splitBasicBlocks[In:Type,Out:Type](b : BlockIR[In,Out], rest : BlockIR2[Out]) : (BlockIR2[In],Seq[(AnyRef,BlockIR2[_])]) = b match {
    case BranchIR(condition,yes,no) => {
      if (containsJumps(yes) || containsJumps(no)) then {
        val (yBlock, yBlocks) = splitBasicBlocks(yes,JumpIR2(rest))
        val (nBlock, nBlocks) = splitBasicBlocks(no,JumpIR2(rest))
        (BranchIR2[In](condition,yBlock,nBlock), Seq((rest,rest)) ++ yBlocks ++ nBlocks)
      } else {
        (BeforeIR2[In,Out](ctx => compileJumplessBlock(b, ctx), rest), Seq())
      }
    }
    case SeqIR(left,right) => {
      implicit val _ = left.tOut
      val (rBlock, rBlocks) = splitBasicBlocks(right,rest)
      val (lBlock, lBlocks) = splitBasicBlocks(left, rBlock)
      (lBlock, lBlocks ++ rBlocks)
    }
    case CallIR(key) => {
      // tail-call optimisation
      if (rest == ReturnIR2[Any]()) {
        (JumpIR2(key), Seq())
      } else {
        (CallIR2(key,(key,rest)), Seq(((key,rest),rest)))
      }
    }
    case SimpleIR(fn) => {
      (BeforeIR2[In,Out](fn, rest), Seq())
    }
    case PreserveArgIR(bb) => {
      type BBout = bb.out
      implicit val e1 = bb.tOut
      if (containsJumps(bb)) then {
        val (block, otherBlocks) = splitBasicBlocks(bb, PopArgIR2[BBout,In](rest))
        (PushArgIR2(block), otherBlocks)
      } else {
        (BeforeIR2[In,(In,BBout)](ctx => compileJumplessBlock(b, ctx), rest), Seq())
      }
    }
    case RecoverIR(successPath, failPath) => {
      val (successBlock, successBlocks) = splitBasicBlocks(successPath, JumpIR2(rest))
      val (failBlock, failBlocks) = splitBasicBlocks(failPath, JumpIR2(rest))
      (PushRecoverIR2(failBlock, successBlock), Seq((failBlock,failBlock), (rest,rest)) ++ successBlocks ++ failBlocks)
    }
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
      val compiler = BlockCompiler(seqCtx)
      val blocks = compiler.computeBlocks(g)
      val inlinedBlocks = performInlining(blocks)
      val basicBlocks : List[(AnyRef,BlockIR2[_])] = List(inlinedBlocks : _*).flatMap(block => {
        val (key,b) = block
        implicit val _ = b.tIn
        implicit val _1 = b.tOut
        val (root, basics) = splitBasicBlocks(b, ReturnIR2())
        List((key,root)) ++ basics
      })
      val pcMap = Map[AnyRef,Int](basicBlocks.zipWithIndex.map(t => t match {
        case ((key,_),idx) => (key, idx)
      }) : _*)
      '{
        var stackPC : List[Int] = Nil
        var stackData : List[Any] = Nil
        var stackRecover : List[(Int,Any,List[Int],List[Any])] = Nil
        var pc : Int = 0
        var register : Any = null
        var loop = true
        while(loop) {
          ${
            def codegen[In:Type](b : BlockIR2[In], argument : Expr[In]) : Expr[Unit] = b match {
              case BranchIR2(condition,yes,no) => '{
                //println("condition")
                if ${condition(argument)}
                then ${codegen(yes,argument)}
                else ${codegen(no,argument)}
              }
              case bef@BeforeIR2(map,next) => {
                def fn[In:Type,In2:Type](a : Expr[In], bef : BeforeIR2[In,In2]) = bef.map(new {
                  def arg = a
                  def fail = '{
                    //println("fail")
                    stackRecover match {
                      case Nil => {
                        loop = false
                        register = null
                      }
                      case hd :: tl => {
                        val (rpc, rreg, rstackPC, rstackData) = hd
                        pc = rpc
                        register = rreg
                        stackPC = rstackPC
                        stackData = rstackData
                        stackRecover = tl
                      }
                    }
                  }
                  def succeed(v : Expr[In2]) = '{
                    val result = ${v}
                    //print("succeed"); println(result)
                    ${codegen(bef.next, '{result})}
                  }
                })
                fn(argument,bef)(implicitly[Type[In]],next.tIn)
              }
              case CallIR2(key,ret) => '{
                register = ${argument}
                pc = ${pcMap(key).toExpr}
                //print("call "); println(pc)
                stackPC = ${pcMap(ret).toExpr} :: stackPC
              }
              case JumpIR2(key) => '{
                register = ${argument}
                pc = ${pcMap(key).toExpr}
                //print("jump "); println(pc)
              }
              case ReturnIR2() => '{
                register = ${argument}
                stackPC match {
                  case Nil => loop = false
                  case hd :: tl => {
                    pc = hd
                    //print("return "); println(pc)
                    stackPC = tl
                  }
                }
              }
              case PushArgIR2(bb) => '{
                val pushedArg = ${argument}
                stackData = pushedArg :: stackData
                ${codegen(bb, '{pushedArg})}
              }
              case pop@PopArgIR2(bb) => {
                implicit val e1 = pop.tArg
                type TA = pop.arg
                '{
                  val (stackTop :: stackTail) = stackData // fails if stack is empty, should never happen
                  val poppedArg = (stackTop.asInstanceOf[TA], ${argument})
                  stackData = stackTail
                  ${codegen(bb, '{poppedArg})}
                }
              }
              case PushRecoverIR2(failKey, bb) => '{
                val pushedArg = ${argument}
                stackRecover = (${pcMap(failKey).toExpr}, pushedArg, stackPC, stackData) :: stackRecover
                ${codegen(bb, '{pushedArg})}
              }
            }
            basicBlocks.foldRight[Expr[Unit]]('{???})((tpl, otherwise) => tpl match {
              case (key, b) => {
                def fn[TI:Type](b : BlockIR2[TI]) = '{
                  if pc == ${pcMap(key).toExpr}
                  then ${codegen(b,'{register.asInstanceOf[${b.tIn}]})}
                  else ${otherwise}
                }
                fn(b)(b.tIn)
              }
            })
          }
        }
        if(register == null)
        then None
        else Some(register.asInstanceOf[T])
      }
    })
  }

  def main(argv : Array[String]) : Unit = {
    import scala.quoted.Toolbox.Default._
    object vv {
      val v : Grammar[Unit,Int,Int] = term(1) <|> term(2) <|> v
      val v2 : Grammar[Unit,(Int,Int),Int] = (term(1) ++ term(2)) <|> v2
    }
    val expr = compile[Int,Int,List](vv.v)
    println(expr.show)
    val parser = expr.run
    //println(parser(List()))
    println(parser(List(1)))
    println(parser(List(2)))
  }
}

