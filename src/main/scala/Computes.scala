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

sealed trait RewriteContext {
  def get(index : Int) : Computes[_]
  def getType(index : Int) : Type[_]
}

sealed abstract class CRewrite[T] {
  //def flatMap[T2](fn : Computes[T] => CRewrite[T2]) : CRewrite[T2] =

}
case class NoRewrite[T]() extends CRewrite[T]
case class ClassTagMatchRewrite[T, R <: Rule[T] : ClassTag]() extends CRewrite[T] {
  val tag = classTag[R]
}

sealed trait Typed[T] {
  def getType given RewriteContext : Type[T]
}

sealed abstract class CHandle[T] extends Typed[T] {
  val index : Int

  def get given (ctx : RewriteContext) : Computes[T] =
    ctx.get(index).asInstanceOf[Computes[T]]

  def getType given (ctx : RewriteContext) : Type[T] =
    ctx.getType(index).asInstanceOf[Type[T]]

  def findByRule[R <: Rule[T] : ClassTag] given (ctx : RewriteContext) : CRewrite[T] =
    ClassTagMatchRewrite[T, R]()
}

sealed abstract class CNHandle[T] extends Typed[T] {
  val index : Int

  def getType given (ctx : RewriteContext) : Type[T] =
    ctx.getType(index).asInstanceOf[Type[T]]
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
  def getType given QuoteContext given RewriteContext : Type[T]
  type ComputesMembers <: Tuple
  type ComputesRewrites <: Tuple
}

object RuleMagic {
  inline def makeHandles[Index <: Int, TypesAndLabels <: Tuple] : List[AnyRef] =
    inline erasedValue[TypesAndLabels] match {
      case _ : Unit => Nil
      case _ : ((CNHandle[t],_) *: tail) => {
        type T = t
        new CNHandle[T]() {
          val index : Int = inline constValue[Index] match { case idx => idx }
        } :: makeHandles[S[Index],tail]
      }
      case _ : ((CHandle[t],_) *: tail) => {
        type T = t
        new CHandle[T]() {
          val index : Int = inline constValue[Index] match { case idx => idx }
        } :: makeHandles[S[Index],tail]
      }
      case _ : ((_, label) *: _) => {
        inline constValue[label] match {
          case labelStr => error(code"Rule members must all be wrapped in CHandle or CNHandle, $labelStr is not")
        }
      }
    }

  inline def makeContext[Types <: Tuple](handles : List[AnyRef]) given RewriteContext <: Any =
    inline erasedValue[Types] match {
      case _ : Unit => ()
      case _ : (CNHandle[t] *: tl) => new {
        val innerCtx = makeContext[tl](handles.tail)
        given as Type[t] = handles.head.asInstanceOf[Typed[t]].getType
        import given innerCtx._
      }
      case _ : (CHandle[t] *: tl) => new {
        val innerCtx = makeContext[tl](handles.tail)
        given as Type[t] = handles.head.asInstanceOf[Typed[t]].getType
        import given innerCtx._
      }
    }

  inline def withContext[T,Types <: Tuple](handles : List[AnyRef], base : =>Type[T]) given RewriteContext : Type[T] =
    inline erasedValue[Types] match {
      case _ : Unit => base
      case _ : (CNHandle[t] *: tl) => {
        given as Type[t] = handles.head.asInstanceOf[Typed[t]].getType
        withContext[T,tl](handles.tail, base)
      }
      case _ : (CHandle[t] *: tl) => {
        given as Type[t] = handles.head.asInstanceOf[Typed[t]].getType
        withContext[T,tl](handles.tail, base)
      }
    }

  inline def derived[R <: Rule[_]] given (m : Mirror.ProductOf[R]) <: RuleMagic[R] = new RuleMagic[R] {
    val handles = makeHandles[Tuple.Size[m.MirroredElemTypes],Tuple.Zip[m.MirroredElemTypes,m.MirroredElemLabels]]
    def makeInstance : R = m.fromProduct(ArrayProduct(handles.toArray))
    def membersToList(members : ComputesMembers) : List[Computes[_]] = members.toArray.toList.asInstanceOf[List[Computes[_]]]
    type ComputesMembers = Tuple.Map[m.MirroredElemTypes,[m]=>>m match {
      case CNHandle[t] => ComputesName[t]
      case CHandle[t] => Computes[t]
    }]
    type ComputesRewrites = Tuple.Map[m.MirroredElemTypes,[m]=>>m match {
      case CNHandle[t] => Unit // FIXME
      case CHandle[t] => CRewrite[t]
    }]
  }
}

abstract class Rule[T] given (t : Type[T]) {
  given theType as Type[T] = t
  def rewrite : given RewriteContext => CRewrite[T] = NoRewrite()
  def lower : given RewriteContext => Computes[T]
}

sealed abstract class Computes[T] {
  def key given (keyCtx : KeyContext) : ComputesKey = keyCtx.getKeyOf(this)
}

object Computes {

  inline def construct[R <: Rule[_]] given (magic : RuleMagic[R]) : (magic.ComputesMembers)=>Computes[magic.T] =
    (members : magic.ComputesMembers) =>
      ComputesComposite[magic.T,R](magic.makeInstance, magic.membersToList(members))

  inline def expr[Members <: Tuple, T, F](
    members : Members,
    fn : F
  ) given Tuple.IsMappedBy[Computes][Members] given (tpl : TupledFunction[F,Tuple.Map[Tuple.InverseMap[Members,Computes],Expr]=>given QuoteContext=>Expr[T]]) : Computes[T] =
    ComputesExpr[T](members.toArray.toList, members => tpl.tupled(fn)(Tuple.fromArray(members.toArray).asInstanceOf[Members]))
}

final case class ComputesComposite[T, R <: Rule[T]](val rule : R, val members : List[Computes[_]]) given (magic_ : RuleMagic[R]) extends Computes[T] {
  val magic = magic_
}

// generate expressions via subclassing, allow simple version w/ all fields available and complex version w/ choice of ordering
final case class ComputesExpr[T](val fn : List[Expr[_]]=>Expr[_], val members : List[Computes[_]]) extends Computes[T]

final class ComputesName[T] extends Computes[T]

// test

case class AddInts[A,B](lhs : CHandle[A], rhs : CHandle[B]) extends Rule[(A,B)] derives RuleMagic {
  def lower = ??? //Computes.constructor[AddInts]((lhs.get, rhs.get))
}

