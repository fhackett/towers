package polyparse

import scala.quoted._
//import scala.quoted.Toolbox.Default._


sealed trait A[T:Type] {
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
}

/*object PolyParse {

  sealed trait Grammar[T](_tType : Type[T]) {
    val tType : Type[T] = _tType
  }

  sealed trait Value[T] {
    def ++[T2](v2 : Value[T2]) : Value[(T,T2)] = PairValue(this, v2)
    def map[T2](fn : Expr[T] => Expr[T2]) : Value[T2] = MappedValue(this, fn)
  }

  case class PlainValue[T : Liftable](val v : T) extends Value[T]
  case class MappedValue[T1,T2](val v : Value[T1], val fn : Expr[T1] => Expr[T2]) extends Value[T2]
  case class PairValue[T1,T2](val v1 : Value[T1], val v2 : Value[T2]) extends Value[(T1,T2)]
  class RegisterValue[T] extends Value[T]

  private case class Terminal[T:Type](val v : Value[T]) extends Grammar[T](implicitly[Type[T]])
  private case class Tuple[A,B](val left : Grammar[A], val right : Grammar[B]) extends Grammar[(A,B)]('[(~left.tType,~right.tType)])
  //private case class IgnoreLeft[T](val left : Grammar[T], val right : Grammar[T]) extends Grammar[T]
  //private case class IgnoreRight[T](val left : Grammar[T], val right : Grammar[T]) extends Grammar[T]
  private case class Disjunction[T](val left : Grammar[T], val right : Grammar[T]) extends Grammar[T](left.tType)
  private case class Condition[T](val g : Grammar[T], val cond : Expr[T] => Expr[Boolean]) extends Grammar[T](g.tType)
  private case class PutValue[T:Type](val v : Value[T]) extends Grammar[T](implicitly[Type[T]])
  private case class TakeValue[T1,T2](val g : Grammar[T1], val v : RegisterValue[T1], val gg : Grammar[T2]) extends Grammar[T2](gg.tType)
  private case class Mapping[T1,T2:Type](val from : Grammar[T1], val m : Expr[T1] => Expr[T2]) extends Grammar[T2](implicitly[Type[T2]])
  //private case class AppliedLam[A,T](val reg : RegisterValue[A], val arg : Value[A], val body : Grammar[T]) extends Grammar[T]
  private class Recursion[T:Type](_g : =>Grammar[T]) extends Grammar[T](implicitly[Type[T]]) {
    lazy val g = _g
  }

  //sealed abstract class GLam[-Arg, SR <: GLam[_,SR]] {
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
  }

  private def maybeRecurse[T:Type](g : =>Grammar[T]) : Grammar[T] = if g == null then new Recursion(g) else g

  implicit class MaybeRecursion[T:Type](g : =>Grammar[T]) {
    def <|>(other : =>Grammar[T]) : Grammar[T] = Disjunction(maybeRecurse(g), maybeRecurse(other))
    def ++[Other:Type](other : =>Grammar[Other]) : Grammar[(T,Other)] = Tuple(maybeRecurse(g), maybeRecurse(other))
    def map[T2:Type](fn : Expr[T] => Expr[T2]) : Grammar[T2] = Mapping[T,T2](maybeRecurse(g), fn)
    def ??(cond : Expr[T] => Expr[Boolean]) : Grammar[T] = Condition(maybeRecurse(g), cond)
    def $$[T2:Type](fn : Value[T] => Grammar[T2]) : Grammar[T2] = {
      val reg = new RegisterValue[T]()
      TakeValue(maybeRecurse(g), reg, fn(reg))
    }
  }

  def const[T:Liftable:Type](v : T) : Value[T] = PlainValue(v)
  
  def value[T:Type](v : Value[T]) : Grammar[T] = PutValue(v)

  def term[T:Type](v : Value[T]) : Grammar[T] = Terminal(v)

  //def lam[A,T](scope : Value[A] => Grammar[T]) : Lam[A,T] = {
    val reg = new RegisterValue[A]()
    Lam(reg, scope(reg))
  }

  def lam[A,L <: GLam[_,L]](scope : Value[A] => L) : PLam[A,L] = {
    val reg = new RegisterValue[A]()
    PLam(reg, scope(reg))
  }

  trait SequenceContext[T,SeqT] {
    type Mark
    def mark() : Expr[Mark]
    def restore(m : Expr[Mark]) : Expr[Unit]
    def peek() : Expr[T]
    def isEOF() : Expr[Boolean]
    def next() : Expr[Unit]
  }

  def makeListContext[T:Type,Result:Type](fn : SequenceContext[T,List[T]] => Expr[Result]) = '((list_ : List[T]) => {
    var list = list_
    ~fn(new {
      type Mark = List[T]
      def mark() : Expr[Mark] = '{ list }
      def restore(m : Expr[Mark]) : Expr[Unit] = '{ list = ~m }
      def peek() : Expr[T] = '{ list.head }
      def isEOF() : Expr[Boolean] = '{ list.isEmpty }
      def next() : Expr[Unit] = '{ list = list.tail }
    })
  })

  def compile[T:Type,ST:Type,SeqT:Type](g : Grammar[T], mkCtx : (SequenceContext[ST,SeqT] => Expr[Option[T]]) => Expr[SeqT => Option[T]]) : Expr[SeqT => Option[T]] = {
    def findRecursions[T](g : Grammar[T]) : Set[Grammar[_]] = g match {
      case Terminal(_) => Set.empty
      case Tuple(a,b) => findRecursions(a) & findRecursions(b)
      case Disjunction(a,b) => findRecursions(a) & findRecursions(b)
      case Condition(a,_) => findRecursions(a)
      case PutValue(_) => Set.empty
      case TakeValue(a,_,b) => findRecursions(a) & findRecursions(b)
      case Mapping(a,_) => findRecursions(a)
      case r : Recursion[T] => Set(r.g)
    }
    val recursions = findRecursions(g)

    mkCtx(ctx => {
      def handleRec[T:Type](gg : Grammar[T], recMap : Map[AnyRef,Expr[() => _]]) : Expr[Option[T]] = {
        if recursions.contains(g) then '{
          //def rec() : Option[T] = ~codegen(g, recMap.+(gg, '(() => rec())))
          rec()
          None
        } else '{
          ~codegen(gg, recMap)
        }
      }
      def codegen[T:Type](g : Grammar[T], recMap : Map[AnyRef,Expr[() => Any]]) : Expr[Option[T]] = g match {
        case Terminal(v) => '{ if !(~ctx.isEOF()) then None //~ctx.peek() FIXME  else None }
        case Tuple(a,b) => '{ 
          (~handleRec(a, recMap)(a.tType)).flatMap((v1 : ~a.tType) => (~handleRec(b, recMap)(b.tType)).map((v2 : ~b.tType) => (v1, v2)))
        }
        case Disjunction(a,b) => '{
          (~handleRec(a, recMap)).orElse(~handleRec(b, recMap))
        }
        case Condition(a,cond) => '{
          (~handleRec(a, recMap)).flatMap(v => if ~cond('(v)) then Some(v) else None)
        }
        case PutValue(v) => '{ None } // FIXME 
        case TakeValue(a,v,b) => '{ None } // FIXME 
        case Mapping(a,fn) => '{
          (~handleRec(a, recMap)(a.tType)).map((v : ~a.tType) => ~fn('(v)))
        }
        case r : Recursion[T] => '{
          (~recMap.get(r.g).get()).asInstanceOf[() => Option[T]]()
        }
      }
      handleRec(g, Map.empty)
    })

    //def impl[T](g : Grammar[T]) = {
      
    }
    '(s => None) 
  }
}*/

