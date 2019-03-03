package polyparse

import scala.quoted._
//import scala.quoted.Toolbox.Default._


/*sealed trait A[T:Type] {
  val t = implicitly[Type[T]]
}

case class B[T:Liftable:Type](val v : T) extends A[T] {
  val liftable = implicitly[Liftable[T]]
}
case class C[T1:Type,T2:Type](val v1 : A[T1], val v2 : A[T2]) extends A[(T1,T2)]

object D {
  def proc[T:Type](a : A[T]) : Expr[T] = a match {
    case b@B(v) => v.toExpr(b.liftable)
    case C(v1,v2) => {
      implicit val v1t = v1.t
      implicit val v2t = v2.t
      '( (~proc(v1), ~proc(v2)) )
    }
  }
} */

sealed trait Grammar[T:Type,ET:Type] {
  val tType = implicitly[Type[T]]
  val eType = implicitly[Type[ET]]
}

sealed trait Value[T] {
  def ++[T2](v2 : Value[T2]) : Value[(T,T2)] = PairValue(this, v2)
  def map[T2](fn : Expr[T] => Expr[T2]) : Value[T2] = MappedValue(this, fn)
}

case class PlainValue[T : Liftable](val v : T) extends Value[T] {
  val liftable = implicitly[Liftable[T]]
}
case class MappedValue[T1,T2](val v : Value[T1], val fn : Expr[T1] => Expr[T2]) extends Value[T2]
case class PairValue[T1,T2](val v1 : Value[T1], val v2 : Value[T2]) extends Value[(T1,T2)]
class RegisterValue[T] extends Value[T]

private case class Terminal[T:Type](val v : Value[T]) extends Grammar[T,T]
private case class Tuple[A:Type,B:Type,ET:Type](val left : Grammar[A,ET], val right : Grammar[B,ET]) extends Grammar[(A,B),ET]
//private case class IgnoreLeft[T](val left : Grammar[T], val right : Grammar[T]) extends Grammar[T]
//private case class IgnoreRight[T](val left : Grammar[T], val right : Grammar[T]) extends Grammar[T]
private case class Disjunction[T:Type,ET:Type](val left : Grammar[T,ET], val right : Grammar[T,ET]) extends Grammar[T,ET]
private case class Condition[T:Type,ET:Type](val g : Grammar[T,ET], val cond : Expr[T] => Expr[Boolean]) extends Grammar[T,ET]
private case class PutValue[T:Type,ET:Type](val v : Value[T]) extends Grammar[T,ET]
private case class TakeValue[T1,T2:Type,ET:Type](val g : Grammar[T1,ET], val v : RegisterValue[T1], val gg : Grammar[T2,ET]) extends Grammar[T2,ET]
private case class Mapping[T1,T2:Type,ET:Type](val from : Grammar[T1,ET], val m : Expr[T1] => Expr[T2]) extends Grammar[T2,ET]
//private case class AppliedLam[A,T](val reg : RegisterValue[A], val arg : Value[A], val body : Grammar[T]) extends Grammar[T]
private class Recursion[T:Type,ET:Type](_g : =>Grammar[T,ET]) extends Grammar[T,ET] {
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

trait MakeSequenceContext[SeqT <: [ET] => Any] {
  def makeCtx[ET:Type,Result:Type](fn : SequenceContext[ET] => Expr[Result]) : Expr[SeqT[ET] => Result]
}

object PolyParse {

  /*sealed abstract class GLam[-Arg, SR <: GLam[_,SR]] {
    type SResult = SR
    def sub[A2](reg2 : RegisterValue[A2], arg : Value[A2]) : SR
  }

  case class Lam[A,T](val reg : RegisterValue[A], val g : Grammar[T]) extends GLam[A,Lam[A,T]] {
    def apply(arg : Value[A]) : Grammar[T] = AppliedLam(reg, arg, g)
    def sub[A2](reg2 : RegisterValue[A2], arg : Value[A2]) : Lam[A,T] = Lam(reg,AppliedLam(reg2, arg, g))
  }
  case class PLam[A,L<:GLam[_,L]](val reg : RegisterValue[A], val l : L) extends GLam[A,PLam[A,L]] {
    def apply(arg : Value[A]) : l.SResult = l.sub(reg, arg)
    def sub[A2](reg2 : RegisterValue[A2], arg : Value[A2]) : PLam[A,L] = PLam[A,L](reg, l.sub(reg2, arg))
  }*/

  private def maybeRecurse[T:Type,ET:Type](g : =>Grammar[T,ET]) : Grammar[T,ET] = if g == null then new Recursion(g) else g

  implicit class MaybeRecursion[T:Type,ET:Type](g : =>Grammar[T,ET]) {
    def <|>(other : =>Grammar[T,ET]) : Grammar[T,ET] = Disjunction(maybeRecurse(g), maybeRecurse(other))
    def ++[Other:Type](other : =>Grammar[Other,ET]) : Grammar[(T,Other),ET] = Tuple(maybeRecurse(g), maybeRecurse(other))
    def map[T2:Type](fn : Expr[T] => Expr[T2]) : Grammar[T2,ET] = Mapping(maybeRecurse(g), fn)
    def ??(cond : Expr[T] => Expr[Boolean]) : Grammar[T,ET] = Condition(maybeRecurse(g), cond)
    def $$[T2:Type](fn : Value[T] => Grammar[T2,ET]) : Grammar[T2,ET] = {
      val reg = new RegisterValue[T]()
      TakeValue(maybeRecurse(g), reg, fn(reg))
    }
  }

  def const[T:Liftable:Type](v : T) : Value[T] = PlainValue(v)
  
  def value[T:Type,ET:Type](v : Value[T]) : Grammar[T,ET] = PutValue(v)

  def term[T:Type](v : Value[T]) : Grammar[T,T] = Terminal(v)

  /*def lam[A,T](scope : Value[A] => Grammar[T]) : Lam[A,T] = {
    val reg = new RegisterValue[A]()
    Lam(reg, scope(reg))
  }

  def lam[A,L <: GLam[_,L]](scope : Value[A] => L) : PLam[A,L] = {
    val reg = new RegisterValue[A]()
    PLam(reg, scope(reg))
  }*/

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

  def compile[T:Type,ET:Type,Seq <: [ET] => Any :MakeSequenceContext](g : Grammar[T,ET])(implicit seqT : Type[Seq[T]]) : Expr[Seq[ET] => Option[T]] = {
    def findRecursions[T,ET](g : Grammar[T,ET]) : Set[Grammar[_,_]] = g match {
      case Terminal(_) => Set.empty
      case Tuple(a,b) => findRecursions(a) | findRecursions(b)
      case Disjunction(a,b) => findRecursions(a) | findRecursions(b)
      case Condition(a,_) => findRecursions(a)
      case PutValue(_) => Set.empty
      case TakeValue(a,_,b) => findRecursions(a) | findRecursions(b)
      case Mapping(a,_) => findRecursions(a)
      case r : Recursion[T,ET] => Set(r.g)
    }
    val recursions = findRecursions(g)
    println(recursions)

    implicitly[MakeSequenceContext[Seq]].makeCtx(ctx => {
      def handleRec[T:Type](g : Grammar[T,ET], recMap : Map[AnyRef,Expr[Option[Any]]]) : Expr[Option[T]] = {
        if recursions.contains(g) then '{
          def rec() : Option[T] = ~codegen(g, recMap.+((g, '(rec()))))
          rec()
        } else '{
          ~codegen(g, recMap)
        }
      }
      def valueCodegen[T:Type](v : Value[T]) : Expr[T] = v match {
        case p@PlainValue(v) => v.toExpr(p.liftable)
      }
      def codegen[T:Type](g : Grammar[T,ET], recMap : Map[AnyRef,Expr[Option[Any]]]) : Expr[Option[T]] = g match {
        case Terminal(v) => '{
          if !(~ctx.isEOF()) then {
            val p = ~ctx.peek()
            if p == ~valueCodegen(v) then {
              ~ctx.next()
              Some(p)
            } else None
          } else None
        }
        case Tuple(a,b) => {
          implicit val at = a.tType
          implicit val bt = b.tType
          '{ 
            (~handleRec(a, recMap)).flatMap(v1 => (~handleRec(b, recMap)).map(v2 => (v1, v2)))
          }
        }
        case Disjunction(a,b) => '{
          (~handleRec(a, recMap)).orElse(~handleRec(b, recMap))
        }
        case Condition(a,cond) => '{
          (~handleRec(a, recMap)).flatMap(v => if ~cond('(v)) then Some(v) else None)
        }
        case PutValue(v) => '{ None } // FIXME 
        case TakeValue(a,v,b) => '{ None } // FIXME 
        case Mapping(a,fn) => {
          implicit val at = a.tType
          '{
            (~handleRec(a, recMap)).map(v => ~fn('(v)))
          }
        }
        case r : Recursion[T,ET] => '{
          (~recMap.get(r.g).get.asInstanceOf[Expr[Option[T]]])
        }
      }
      handleRec(g, Map.empty)
    })
  }

  def runTest = {
    import scala.quoted.Toolbox.Default._
    object vv {
      val v : Grammar[(Int,Int),Int] = (term(const(1)) ++ term(const(2))) <|> v
    }
    compile(vv.v).show
  }
}

