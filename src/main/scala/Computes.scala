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

sealed abstract class Rule[T] {
  type Members <: Tuple
  type ComputesMembers <: Tuple
  def make(members : ComputesMembers) : Computes[T]
}

object Rule {
  
  abstract class R[T] {
    
  }
}

object Computes { 

  private inline def makeHandles[Index <: Int, Members <: Tuple](ownerRef : =>Computes[_]) : Members = inline erasedValue[Members] match {
    case _ : Unit => ().asInstanceOf[Members]
    case _ : (CHandle[hd] *: tl) => (new CHandle[hd] {
      val index = constValue[Index]
      lazy val owner = ownerRef
    } *: makeHandles[S[Index], tl](ownerRef)).asInstanceOf[Members]
  }

  inline def rule[Handles <: Tuple, F, T](body : F)(given tpl : TupledFunction[F,Handles=>Rule.R[T]])(given Tuple.IsMappedBy[CHandle][Handles]) <: Rule[T] =
    new Rule[T] {
      type Members = Tuple.InverseMap[Handles,CHandle]
      type ComputesMembers = Tuple.Map[Members,Computes]
      def make(members : ComputesMembers) : Computes[T] = {
        lazy val ruleR : Rule.R[T] = tpl.tupled(body)(makeHandles[0,Handles](result))
        lazy val result : Computes[T] = ComputesComposite(ruleR, members.toArray.toList.asInstanceOf[List[Computes[_]]])
        result
      }
    }
}

final case class ComputesComposite[T, R <: Rule.R[T]](val rule : R, val members : List[Computes[_]]) extends Computes[T]

final class ComputesName[T] extends Computes[T]

// test

def TupleConcat[L <: Tuple, R <: Tuple] = Computes.rule {
  (lhs : CHandle[L], rhs : CHandle[R]) => new Rule.R[Tuple.Concat[L,R]] {
    
  }
}

