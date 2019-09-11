package towers.computes

import Predef.{any2stringadd => _, _} // allow implicits to override +

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}
import scala.collection.{Seq}
import scala.collection.immutable.TreeSet

import scala.deriving._
import scala.quoted._
import scala.tasty._
import scala.compiletime._

sealed abstract class ComputesKey
case object NoKey extends ComputesKey
final case class ComputesKeyI(val i : Int) extends ComputesKey

trait KeyContext {
  def getKeyOf(obj : AnyRef) : ComputesKey
}

sealed trait RewriteContext {
  def get(index : Int) : Computes[_]
}

sealed abstract class CRewrite[T]

sealed abstract class CHandle[T] {
  def tType given QuoteContext : Type[T]
  val index : Int

  def get given (ctx : RewriteContext) : Computes[T] =
    ctx.get(index).asInstanceOf[Computes[T]]

  def findByRule[R <: Rule[_]] given (ctx : RewriteContext) : CRewrite[T] = ???
}

sealed abstract class CNHandle[T] {
  def tType given QuoteContext : Type[T]
  val index : Int
}

/*
final case class NoRewrite[T]() extends Rewrite[T]
final case class ResultRewrite[T](val result : Computes[T]) extends Rewrite[T]
final case class MatchRewrite[MatchMembers <: Tuple,MatchT,T,F](
  val handle : Computes[MatchT],
  val rulesToMatch : Rules[MatchMembers,MatchT],
  val next : F
) given TupledFunction[F,Tuple.Map[MatchMembers,[t]=>>ComputesHandle[t]]=>Rewrite[T]] extends Rewrite[T]
final case class ChooseRewrite[T](val first : Rewrite[T], val second : Rewrite[T]) extends Rewrite[T]*/

sealed trait RuleMagic[R <: Rule[_]] {
  type T = R match { case Rule[t] => t }
  val handles : List[AnyRef]
  def makeInstance : R
  def membersToList(members : ComputesMembers) : List[Computes[_]]
  def tType given QuoteContext : Type[T]
  type ComputesMembers <: Tuple
}

object RuleMagic {
  inline def makeHandles[Index <: Int, TypesAndLabels <: Tuple] : List[AnyRef] =
    inline erasedValue[TypesAndLabels] match {
      case _ : Unit => Nil
      case _ : ((CNHandle[t],_) *: tail) => {
        type T = t
        new CNHandle[T]() {
          def tType given QuoteContext : Type[T] = implicit match { case t : Type[T] => t }
          val index : Int = inline constValue[Index] match { case idx => idx }
        } :: makeHandles[S[Index],tail]
      }
      case _ : ((CHandle[t],_) *: tail) => {
        type T = t
        new CHandle[T]() {
          def tType given QuoteContext : Type[T] = implicit match { case t : Type[T] => t }
          val index : Int = inline constValue[Index] match { case idx => idx }
        } :: makeHandles[S[Index],tail]
      }
      case _ : ((_, label) *: _) => {
        inline constValue[label] match {
          case labelStr => error(code"Rule members must all be wrapped in CHandle or CNHandle, $labelStr is not")
        }
      }
    }

  inline def derived[R <: Rule[_]] given (m : Mirror.ProductOf[R]) <: RuleMagic[R] = new RuleMagic[R] {
    val handles = makeHandles[Tuple.Size[m.MirroredElemTypes],Tuple.Zip[m.MirroredElemTypes,m.MirroredElemLabels]]
    def makeInstance : R = m.fromProduct(ArrayProduct(handles.toArray))
    def membersToList(members : ComputesMembers) : List[Computes[_]] = members.toArray.toList.asInstanceOf[List[Computes[_]]]
    def tType given QuoteContext : Type[T] = implicit match { case t : Type[T] => t }
    type ComputesMembers = Tuple.Map[m.MirroredElemTypes,[m]=>>m match {
      case CNHandle[t] => ComputesName[t]
      case CHandle[t] => Computes[t]
    }]
  }
}

abstract class Rule[T] {
  def rewrite : given RewriteContext => CRewrite[T]
  def lower : given RewriteContext => Computes[T]
}

sealed abstract class Computes[T] {
  //def tType given QuoteContext : Type[T]
  def key given (keyCtx : KeyContext) : ComputesKey = keyCtx.getKeyOf(this)
}

object Computes {

  inline def constructor[R <: Rule[_]] given (magic : RuleMagic[R]) : (magic.ComputesMembers)=>Computes[magic.T] =
    (members : magic.ComputesMembers) =>
      ComputesComposite[magic.T,R](magic.makeInstance, magic.membersToList(members))
}

final class ComputesComposite[T, R <: Rule[T]](val rule : R, val members : List[Computes[_]]) given (magic_ : RuleMagic[R]) extends Computes[T] {
  val magic = magic_
}

final class ComputesName[T] extends Computes[T]

// test

case class AddInts(lhs : CHandle[Int], rhs : CHandle[Int]) extends Rule[Int] derives RuleMagic {
  def rewrite = ???
  def lower = ??? //Computes.constructor[AddInts]((lhs.get, rhs.get))
}

