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
  def rewrite(index : Int, fn : (RewriteContext, Computes[_])=>CRewrite[_]) : CRewrite[_]
  def getType(index : Int) : Type[_]
}

sealed trait LowerContext {
  
}

sealed abstract class CRewrite[T] {
  //def flatMap[T2](fn : Computes[T] => CRewrite[T2]) : CRewrite[T2] =

}

case class NoRewrite[T]() extends CRewrite[T]
/*
case class SuccessRewrite[T](val result : Computes[T]) extends CRewrite[T]
case class ClassTagMatchRewrite[T, R <: Rule[T] : ClassTag](val handle : CHandle[T]) extends CRewrite[T] {
  val tag = classTag[R]
}
case class MapRewrite[T1,T2](val mapped : CRewrite[T1], val fn : Computes[T1]=>Computes[T2]) extends CRewrite[T2]
case class FlatMapRewrite[T1,T2](val mapped : CRewrite[T], val fn : Computes[T1]=>CRewrite[T2]) extends CRewrite[T2]*/

sealed abstract class CHandle[T] {
  val index : Int
  lazy val self : Computes[_]

  def findByRule[R <: Rule[T] : ClassTag](given ctx : RewriteContext) : CRewrite[T] =
    ???
    //ClassTagMatchRewrite[T, R](this)
}

sealed trait RuleMagic[R <: Rule[_]] {
  type T = R match { case Rule[t] => t }
  def makeInstance(self : =>Computes[T]) : R
  def membersToList(members : ComputesMembers) : List[Computes[_]]
  type ComputesMembers <: Tuple
}

abstract class Rule[T](given t : Type[T]) {
  given theType : Type[T] = t
  def rewrite : (given RewriteContext) => CRewrite[T] = NoRewrite()
  def lower : (given LowerContext) => Computes[T]
}

object RuleMagic {
  inline def makeHandles[Index <: Int, TypesAndLabels <: Tuple](selfC : =>Computes[_]) : List[CHandle[_]] =
    inline erasedValue[TypesAndLabels] match {
      case _ : Unit => Nil
      case _ : ((CHandle[t],_) *: tail) => {
        type T = t
        new CHandle[T] {
          val index : Int = inline constValue[Index] match { case idx => idx }
          lazy val self = selfC
        } :: makeHandles[S[Index],tail](selfC)
      }
      case _ : ((_, label) *: _) => {
        inline constValue[label] match {
          case labelStr => error(code"Rule members must all be wrapped in CHandle, $labelStr is not")
        }
      }
    }

  inline def derived[R <: Rule[_]](given m : Mirror.Of[R]) <: RuleMagic[R] = new RuleMagic[R] {
    def makeInstance(self : =>Computes[T]) : R = {
      type Size = Tuple.Size[m.MirroredElemTypes]
      type ElemTypesAndLabels = Tuple.Zip[m.MirroredElemTypes,m.MirroredElemLabels]
      inline m match {
        case m : Mirror.ProductOf[R] =>m.fromProduct(ArrayProduct(makeHandles[Size,ElemTypesAndLabels](self).toArray.asInstanceOf[Array[AnyRef]]))
      }
    }
    def membersToList(members : ComputesMembers) : List[Computes[_]] = members.toArray.toList.asInstanceOf[List[Computes[_]]]
    type ComputesMembers = Tuple.Map[m.MirroredElemTypes,[m]=>>m match {
      case CHandle[t] => Computes[t]
    }]
  }
}

sealed abstract class Computes[T] {
  def key(given keyCtx : KeyContext) : ComputesKey = keyCtx.getKeyOf(this)
}

object Computes {

  inline def construct[R <: Rule[_]](given magic : RuleMagic[R]) : (magic.ComputesMembers)=>Computes[magic.T] =
    (members : magic.ComputesMembers) => {
      val result : Computes[magic.T] = ComputesComposite[magic.T,R](magic.makeInstance(result), magic.membersToList(members))
      result
    }

  /*
  inline def constructExpr[R <: ExprRule[_]](given magic : ExprRuleMagic[R]) : (magic.ComputesMembers)=>Computes[magic.T] =
    (members : magic.ComputesMembers) =>
      ComputesExpr[magic.T,R](magic.makeInstance, magic.membersToList(members))

  inline def expr[T, Members <: Tuple, F](members : Members)(fn : F)(given tpl : TupledFunction[F,Tuple.Map[Tuple.InverseMap[Members,Computes],Expr]=>Expr[T]]) : Computes[T] = {
    val memberList = members.toArray.asInstanceOf[Array[Computes[_]]].toList
    val memberHandles : List[CHandle[_]] = memberList.zipWithIndex.map({
      case (mem : Computes[t], i) => new CHandle[t] {
        val index = i
      }
    })
    type PlainMembers = Tuple.InverseMap[Members,Computes]
    ComputesExpr(
      new {
        def render = {
          val exprs = memberHandles.map(_.render)
          val multiBlock : CMultiBlock[PlainMembers] = CBlock.joinTpl(Tuple.fromArray(memberHandles.toArray).asInstanceOf[Tuple.Map[PlainMembers,CHandle]])
          multiBlock.map(tpl.tupled(fn)(_))
        }
      },
      memberList)
  }*/
}

final case class ComputesComposite[T, R <: Rule[T]](val rule : R, val members : List[Computes[_]]) extends Computes[T]

// generate expressions via subclassing, allow simple version w/ all fields available and complex version w/ choice of ordering
/*class Render[T] extends Computes[T] {
  val references : List[CName
  def render : (given RenderContext) => 
}*/

final class ComputesName[T] extends Computes[T]

// test

case class AddInts[A:Type,B:Type](lhs : CHandle[A], rhs : CHandle[B]) extends Rule[(A,B)] derives RuleMagic {
  def lower = ??? //Computes.constructor[AddInts]((lhs.get, rhs.get))
}

