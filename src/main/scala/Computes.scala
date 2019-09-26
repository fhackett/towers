package towers.computes

import Predef.{any2stringadd => _, _} // allow implicits to override +

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}
import scala.collection.{Seq}
import scala.collection.immutable.TreeSet

import scala.deriving._
import scala.quoted._
import scala.tasty._
import scala.compiletime._
import scala.reflect._

sealed abstract class ComputesKey
case object NoKey extends ComputesKey
final case class ComputesKeyI(val i : Int) extends ComputesKey

trait KeyContext {
  def getKeyOf(obj : AnyRef) : ComputesKey
}

sealed abstract class CHandle[T] {
  val index : Int
  lazy val owner : Computes[_]
}

sealed abstract class Computes[T] {
  def key(given keyCtx : KeyContext) : ComputesKey = keyCtx.getKeyOf(this)
}

sealed abstract class Rule {

  protected inline def rule[Handles <: Tuple, F, T : Type]
                 (body : F)
                 (given tpl : TupledFunction[F,Handles=>Rule.R[T]])
                 (given Tuple.IsMappedBy[CHandle][Handles]) <: Rule.Instance[T] = {
    val thisRule = this
    new Rule.Instance[T] {
      val rule = thisRule
      type CHandles = Handles
      type Members = Tuple.InverseMap[Handles,CHandle]
      type ComputesMembers = Tuple.Map[Members,Computes]
      def apply(members : ComputesMembers) : Computes[T] = {
        lazy val handles : Handles = Rule.makeHandles[0,Handles](result)
        lazy val ruleR : Rule.R[T] = tpl.tupled(body)(handles)
        lazy val result : Computes[T] = ComputesComposite(
          this, members.toArray.toList.asInstanceOf[List[Computes[_]]],
          handles.toArray.toList.asInstanceOf[List[CHandle[_]]])
        result
      }
      def matchRewrite(fn : Handles=>Rule.CRewrite[T]) : Rule.CRewrite[T] =
        Rule.MatchRewrite(thisRule, fn)
    }
  }
}

object Rule {

  sealed abstract class CRewrite[T] {
    // TODO
  }

  final case class MatchRewrite[T, R <: Rule, Handles <: Tuple](val rule : R, val fn : Handles=>CRewrite[T]) extends CRewrite[T]

  sealed abstract class Instance[T] {
    val rule : Rule
    type CHandles <: Tuple
    type Members <: Tuple
    type ComputesMembers <: Tuple
    def apply(members : ComputesMembers) : Computes[T]
    def matchRewrite(fn : CHandles=>CRewrite[T]) : CRewrite[T]
  }
  
  abstract class R[T] {
    def rewrite : Any//CRewrite[T]
    def lower : Any//CLower[T]
  }

  private[computes] inline def makeHandles[Index <: Int, Members <: Tuple](ownerRef : =>Computes[_]) : Members = inline erasedValue[Members] match {
    case _ : Unit => ().asInstanceOf[Members]
    case _ : (CHandle[hd] *: tl) => (new CHandle[hd] {
      val index = constValue[Index]
      lazy val owner = ownerRef
    } *: makeHandles[S[Index], tl](ownerRef)).asInstanceOf[Members]
  }
}

object Computes {
  def ref[T](body : (given QuoteContext)=>Computes[T]) : Computes[T] =
    ComputesRef(body)
}

final case class ComputesComposite[T : Type, R <: Rule.Instance[T]](val rule : R, val members : List[Computes[_]], val handles : List[CHandle[_]]) extends Computes[T] {
  val theType = implicitly[Type[T]]
}

final class ComputesName[T : Type] extends Computes[T] {
  //val theType = the[Type[T]]
}

final class ComputesRef[T](val ref : (given QuoteContext)=>Computes[T]) extends Computes[T]

// test

object TupleConcat extends Rule {
  def apply[L <: Tuple : Type, R <: Tuple : Type](given QuoteContext) = rule {
    (lhs : CHandle[L], rhs : CHandle[R]) => new Rule.R[Tuple.Concat[L,R]] {
      def rewrite = ???
      def lower = ???
    }
  }
}

