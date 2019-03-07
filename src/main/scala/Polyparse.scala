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
  def mark() : Expr[Mark]
  def restore(m : Expr[Mark]) : Expr[Unit]
  def peek() : Expr[ET]
  def isEOF() : Expr[Boolean]
  def next() : Expr[Unit]
}

class BlockContext {
  import collection.mutable.Map
  val blocks : Map[Int,Block[_]] = Map.empty
  var nextPC = 0
  def makeBlock[Input](fn : Expr[Input] => Expr[Any]) : Block[Input] = {
    val nBlock = Block(nextPC, fn)
    blocks(nextPC) = nBlock
    nextPC += 1
    nBlock
  }
  /*def reify[Result:Type](initBlock : Block[_,_]) : Expr[Result] = '{
    var pc = ~block.label
    var arg : Any = Null
    var loop = true
    while(loop) {
      ~{
        (0 until nextPC).foldRight('())((i, r) => '{ if pc == ~(i) then {
          arg = ~blocks(i).fn('(arg.asInstanceOf[~[blocks(i).aType]]))
        } else ~r })
      }
    }
  }*/
}

case class Block[Input](val label : Int, val fn : Expr[Input] => Expr[Any]) {
  def goto(input : Expr[Input])(implicit ctx : BlockContext) : Expr[Unit] = {
    '()
  }
}

trait MakeSequenceContext[Seq[_]] {
  def makeCtx[ET:Type,Result:Type](fn : SequenceContext[ET] => Expr[Result]) : Expr[Seq[ET] => Result]
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
    def makeCtx[ET:Type,Result:Type](fn : SequenceContext[ET] => Expr[Result]) : Expr[List[ET] => Result] = '((list_ : List[ET]) => {
      var list = list_
      ~fn(new {
        type Mark = List[ET]
        def mark() : Expr[Mark] = '{ list }
        def restore(m : Expr[Mark]) : Expr[Unit] = '{ list = ~m }
        def peek() : Expr[ET] = '{ list.head }
        def isEOF() : Expr[Boolean] = '{ list.isEmpty }
        def next() : Expr[Unit] = '{ list = list.tail }
      })
    })
  }

  /*def makeControlFlow(fn : Block[Unit,Unit] => Unit) : Expr[Unit] = {
    
  }*/

  def compile[T:Type,ET:Type,Seq[_]:MakeSequenceContext](g : Grammar[Unit,T,ET])(implicit seqT : Type[Seq[T]]) : Expr[Seq[ET] => Option[T]] = {
    def findRecursions[AT,T,ET](g : Grammar[AT,T,ET]) : Set[Grammar[_,_,_]] = g match {
      case Terminal(_) => Set.empty
      case Sequence(a,b) => findRecursions(a) | findRecursions(b)
      case Disjunction(a,b) => findRecursions(a) | findRecursions(b)
      //case Condition(a,_) => findRecursions(a)
      //case PutValue(_) => Set.empty
      //case TakeValue(a,_,b) => findRecursions(a) | findRecursions(b)
      //case Mapping(a,_) => findRecursions(a)
      case r : Recursion[AT,T,ET] => Set(r.g)
    }
    val recursions = findRecursions(g)
    println(recursions)

    implicitly[MakeSequenceContext[Seq]].makeCtx(ctx => {
      def handleRec[AT:Type,T:Type](g : Grammar[AT,T,ET], recMap : Map[AnyRef,Expr[Option[Any]]]) : Expr[Option[T]] = {
        if recursions.contains(g) then '{
          def rec() : Option[T] = ~codegen(g, recMap.+((g, '(rec()))))
          rec()
        } else '{
          ~codegen(g, recMap)
        }
      }
      def codegen[AT:Type,T:Type](g : Grammar[AT,T,ET], recMap : Map[AnyRef,Expr[Option[Any]]]) : Expr[Option[T]] = g match {
        case t@Terminal(v) => {
          implicit val liftable = t.liftable
          '{
            if !(~ctx.isEOF()) then {
              val p = ~ctx.peek()
              if p == ~v.toExpr then {
                ~ctx.next()
                Some(p)
              } else None
            } else None
          }
        }
        case Sequence(a,b) => {
          implicit val at = a.tType
          implicit val aat = a.aType
          implicit val bt = b.tType
          implicit val abt = b.aType
          '{ 
            (~handleRec(a, recMap)).flatMap(v1 => (~handleRec(b, recMap)).map(v2 => (v1, v2)))
          }
        }
        case Disjunction(a,b) => '{
          (~handleRec(a, recMap)).orElse(~handleRec(b, recMap))
        }
        /*case Condition(a,cond) => '{
          (~handleRec(a, recMap)).flatMap(v => if ~cond('(v)) then Some(v) else None)
        }*/
        //case PutValue(v) => '{ None } // FIXME 
        //case TakeValue(a,v,b) => '{ None } // FIXME 
        /*case Mapping(a,fn) => {
          implicit val at = a.tType
          '{
            (~handleRec(a, recMap)).map(v => ~fn('(v)))
          }
        }*/
        case r : Recursion[AT,T,ET] => '{
          (~recMap.get(r.g).get.asInstanceOf[Expr[Option[T]]])
        }
      }
      handleRec(g, Map.empty)
    })
  }

  def runTest = {
    import scala.quoted.Toolbox.Default._
    object vv {
      val v : Grammar[Unit,Int,Int] = term(1) <|> v
      val v2 : Grammar[(Unit,Unit),(Int,Int),Int] = (term(1) ++ term(2)) <|> v2
    }
    compile(vv.v).show
  }
}

