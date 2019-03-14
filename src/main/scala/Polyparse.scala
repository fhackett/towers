package polyparse

import scala.quoted._
//import scala.quoted.Toolbox.Default._


sealed trait Grammar[AT:Type,T:Type,ET:Type] {
  val tType = implicitly[Type[T]]
  val eType = implicitly[Type[ET]]
  val aType = implicitly[Type[AT]]
}

private case class Terminal[T:Type:Liftable](val v : T) extends Grammar[Unit,T,T] {
  val liftable = implicitly[Liftable[T]]
}
private case class ArgumentTerminal[T:Type]() extends Grammar[T,T,T]
private case class ArgToVal[T:Type]() extends Grammar[T,T,Any]
private case class ReadPos() extends Grammar[Unit,Int,Any]
private case class Call[AT1:Type,AT2:Type,T:Type,ET:Type](val arg : Grammar[AT1,AT2,ET], val fn : Grammar[AT2,T,ET]) extends Grammar[AT1,T,ET]
private case class Sequence[LAT:Type,RAT:Type,LT:Type,RT:Type,ET:Type](val left : Grammar[LAT,LT,ET], val right : Grammar[RAT,RT,ET]) extends Grammar[(LAT,RAT),(LT,RT),ET]
private case class Check[AT:Type,ET:Type](val g : Grammar[AT,Any,ET]) extends Grammar[AT,Unit,ET]
private case class Disjunction[AT:Type,T:Type,ET:Type](val left : Grammar[AT,T,ET], val right : Grammar[AT,T,ET]) extends Grammar[AT,T,ET]
private case class Condition[AT:Type,T:Type,ET:Type](val g : Grammar[AT,T,ET], val cond : Expr[T] => Expr[Boolean]) extends Grammar[AT,T,ET]
private case class MapArg[AT1:Type,AT2,T:Type,ET:Type](val to : Grammar[AT2,T,ET], val fn : Expr[AT1] => Expr[AT2]) extends Grammar[AT1,T,ET]
private case class MapVal[AT:Type,T1,T2:Type,ET:Type](val from : Grammar[AT,T1,ET], val fn : Expr[T1] => Expr[T2]) extends Grammar[AT,T2,ET]
private class Recursion[AT:Type,T:Type,ET:Type](_g : =>Grammar[AT,T,ET]) extends Grammar[AT,T,ET] {
  lazy val g = _g
}

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
  def reg[T:Type] : Expr[T]

  def end(v : Expr[Result]) : Expr[Unit]

  def call(label : Label, ret : Label, arg : Expr[Any]) : Expr[Unit]
  def ret(v : Expr[Any]) : Expr[Unit]

  def push(v : Expr[Any]) : Expr[Unit]
  def pop : Expr[Any]
}

trait MakeSequenceContext[Seq[_]] {
  def makeCtx[ET:Type,Result:Type](fn : SequenceContext[ET] => Expr[Result]) : Expr[Seq[ET] => Result]
}

case class BlockCompiler[ET:Type,Result](seqCtx : SequenceContext[ET], flowCtx : ControlFlowContext[Option[Result]],
  recursions : Set[Grammar[_,_,_]], recMap : Map[AnyRef,flowCtx.Label]) {
  def handleRec[AT:Type,T:Type](g : Grammar[AT,T,ET], arg : Expr[AT], yes : Expr[T]=>Expr[Unit], no : Expr[Unit]) : Expr[Unit] = {
    if recursions.contains(g) then {
      val recLabel = flowCtx.block(recLabel => {
        this.copy(recMap=recMap.+((g, recLabel))).computeValue(g, flowCtx.reg[AT], flowCtx.ret(_), flowCtx.end('{None}))
      })
      val retLabel = flowCtx.block(yes(flowCtx.reg[T]))
      flowCtx.call(recLabel, retLabel, arg)
    } else {
      computeValue(g, arg, yes, no)
    }
  }
  def computeValue[AT:Type,T:Type](g : Grammar[AT,T,ET], arg : Expr[AT], yes : Expr[T]=>Expr[Unit], no : Expr[Unit]) : Expr[Unit] = g match {
    case t@Terminal(v) => {
      implicit val _ = t.liftable
      '{
        if ${seqCtx.isEOF} then $no else {
          val curr = ${seqCtx.peek}
          if curr == ${v.toExpr}
          then {
            ${seqCtx.next}
            ${yes('{curr})}
          } else $no
        }
      }
    }
    case Disjunction(l,r) => {
      '{ // this is eager disjunction, TODO "correct" backtracking disjunction option
        if ${speculateReachable(l, arg)}
        then ${computeValue(l, arg, yes, no)}
        else ${computeValue(r, arg, yes, no)}
      }
    }
    case r : Recursion[AT,T,ET] => {
      val retLabel = flowCtx.block(yes(flowCtx.reg[T]))
      flowCtx.call(recMap(r.g), retLabel, arg)
    }
    case _ => ???
  }
  def speculateReachable[AT:Type,T:Type](g : Grammar[AT,T,ET], arg : Expr[AT]) : Expr[Boolean] = g match {
    case t@Terminal(v) => {
      implicit val _ = t.liftable
      '{ !${seqCtx.isEOF} && ${seqCtx.peek} == ${v.toExpr}}
    }
    case Disjunction(l,r) => '{ ${speculateReachable(l, arg)} || ${speculateReachable(r, arg)} }
    case r : Recursion[AT,T,ET] => speculateReachable(r.g, arg) // speculate past calls to avoid redundantly calling parser we know will fail
                                                                // note: this only works if the parser terminates :) ... maybe catch obvious
                                                                // non-termination later
    case _ => ???
  }
}

object PolyParse {

  private def maybeRecurse[AT:Type,T:Type,ET:Type](g : =>Grammar[AT,T,ET]) : Grammar[AT,T,ET] = if g == null then new Recursion(g) else g

  implicit class MaybeRecursion[AT1:Type,T:Type,ET:Type](g : =>Grammar[AT1,T,ET]) {
    def <|>(other : =>Grammar[AT1,T,ET]) : Grammar[AT1,T,ET] = Disjunction(maybeRecurse(g), maybeRecurse(other))
    def ++[AT2:Type,Other:Type](other : =>Grammar[AT2,Other,ET]) : Grammar[(AT1,AT2),(T,Other),ET] = Sequence(maybeRecurse(g), maybeRecurse(other))
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
    var arg : Any = null
    var loop = true
    while(loop) {
      ${
        import collection.mutable.ArrayBuffer
        val blocks = new ArrayBuffer[(Int,Expr[Unit])]
        fn(new {
          type Label = Int
          def block(f : Int=>Expr[Unit]) : Int = {
            val label = blocks.length
            blocks.+=((label, f(label)))
            label
          }
          def reg[T:Type] : Expr[T] = '{arg.asInstanceOf[T]}
          def end(v : Expr[Result]) : Expr[Unit] = '{
            arg = $v
            loop = false
          }
          def call(label : Int, ret : Int, a : Expr[Any]) : Expr[Unit] = '{
            pc = ${label.toExpr}
            arg = $a
            stackPC.push(${ret.toExpr})
          }
          def ret(v : Expr[Any]) : Expr[Unit] = '{
            pc = stackPC.pop
            arg = $v
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
    arg.asInstanceOf[Result]
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
          val compiler = BlockCompiler(seqCtx, flowCtx, recursions, Map.empty.+((g, root)))
          compiler.handleRec(g, '{()}, res => flowCtx.end('{Some($res)}), flowCtx.end('{None}))
        })
      })
    })
  }

  def runTest = {
    import scala.quoted.Toolbox.Default._
    object vv {
      val v : Grammar[Unit,Int,Int] = term(1) <|> v
      val v2 : Grammar[(Unit,Unit),(Int,Int),Int] = (term(1) ++ term(2)) <|> v2
    }
    compile[Int,Int,List](vv.v).show
  }
}

