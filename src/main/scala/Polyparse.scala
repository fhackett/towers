package polyparse

import scala.quoted._
import scala.quoted.Toolbox.Default._

sealed trait Grammar[T] {
  
}

sealed trait Value[T] {

}

object Implicits {
  implicit class SubGrammar[T](g : =>Grammar[T]) {
    def <|>(other : SubGrammar[T]) : Grammar[T] = Disjunction(this, other)
    def +[Other](other : SubGrammar[Other]) : Grammar[(T,Other)] = Tuple(this, other)
  }

}

import Implicits._

case class PlainValue[T : Liftable](val v : T) extends Value[T]
class RegisterValue[T] extends Value[T]

private case class Terminal[T](val v : Value[T]) extends Grammar[T]
private case class Tuple[A,B](val left : SubGrammar[A], val right : SubGrammar[B]) extends Grammar[(A,B)]
private case class IgnoreLeft[T](val left : SubGrammar[T], val right : SubGrammar[T]) extends Grammar[T]
private case class IgnoreRight[T](val left : SubGrammar[T], val right : SubGrammar[T]) extends Grammar[T]
private case class Disjunction[T](val left : SubGrammar[T], val right : SubGrammar[T]) extends Grammar[T]
private case class Condition[A,T](val g : SubGrammar[T], val v : Value[A], val cond : A => Boolean) extends Grammar[T]
private case class AppliedLam[A,T](val reg : RegisterValue[A], val arg : Value[A], val body : SubGrammar[T]) extends Grammar[T]


sealed abstract class GLam[-Arg, SR <: GLam[_,SR]] {
  type SResult = SR
  def sub[A2](reg2 : RegisterValue[A2], arg : Value[A2]) : SR
}

case class Lam[A,T](val reg : RegisterValue[A], val g : SubGrammar[T]) extends GLam[A,Lam[A,T]] {
  def apply(arg : Value[A]) : Grammar[T] = AppliedLam(reg, arg, g)
  def sub[A2](reg2 : RegisterValue[A2], arg : Value[A2]) : Lam[A,T] = Lam(reg,AppliedLam(reg2, arg, g))
}
case class PLam[A,L<:GLam[_,L]](val reg : RegisterValue[A], val l : L) extends GLam[A,PLam[A,L]] {
  def apply(arg : Value[A]) : l.SResult = l.sub(reg, arg)
  def sub[A2](reg2 : RegisterValue[A2], arg : Value[A2]) : PLam[A,L] = PLam[A,L](reg, l.sub(reg2, arg))

}

object Defs {

  implicit def Const2Value[T : Liftable](v : T) : Value[T] = PlainValue(v)

  def term[T](v : Value[T]) : Grammar[T] = Terminal(v)

  def lam[A,T](scope : Value[A] => Grammar[T]) : Lam[A,T] = {
    val reg = new RegisterValue[A]()
    Lam(reg, scope(reg))
  }
  def lam[A,L <: GLam[_,L]](scope : Value[A] => L) : PLam[A,L] = {
    val reg = new RegisterValue[A]()
    PLam(reg, scope(reg))
  }
}

import Defs._

