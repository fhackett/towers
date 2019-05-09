package towers.computes

import scala.collection.mutable.{HashMap, HashSet}

import quoted._
import tasty._

class ComputesKey()

sealed abstract class Computes[Tp : Type] {
  type T = Tp
  val tType = implicitly[Type[T]]
  val key = ComputesKey()
}

abstract class Computable[T : Type] extends Computes[T] {
  def parts : List[Computes[_]]
  def replace(parts : List[Computes[_]]) : Computable[T]

  def tryFold(parts : List[Computes[_]]) : Option[Computes[T]]
  def flatten : Computes[T]
}

class ComputesIndirect[T : Type](c : =>Computes[T]) extends Computes[T] {
  lazy val computes = c
}

class ComputesVar[T : Type]() extends Computes[T]

class ComputesExpr[T : Type](val params : List[Computes[_]], val exprFn : List[Expr[_]] => Expr[T]) extends Computes[T]

object Computes {

  implicit class ComputesFunction[Arg : Type, Result : Type](fn : Computes[Arg] => Computes[Result]) extends Computes[Arg=>Result] {
    var arg = ComputesVar[Arg]() // mutable, or we can't implement mapBody
    val body = fn(arg)

    def mapBody(fn : Computes[Result] => Computes[Result]) : ComputesFunction[Arg,Result] = {
      val mapped = ComputesFunction[Arg,Result](_ => fn(body))
      mapped.arg = arg
      mapped
    }
  }

  def removeRedundantIndirects[T](computes : Computes[T]) : Computes[T] = {
    val ingressCounts = HashMap[ComputesKey,Int]();
    {
      val visitedSet = HashSet[ComputesKey]()
      visitedSet += computes.key
      ingressCounts(computes.key) = 1
      def countIngresses[T](computes : Computes[T]) : Unit = computes match {
        case c : Computable[T] => c.parts.foreach(countIngresses(_))
        case c : ComputesIndirect[T] =>
          if !visitedSet(c.computes.key) then {
            visitedSet += c.computes.key
            ingressCounts(c.computes.key) = 1
            countIngresses(c.computes)
          } else {
            ingressCounts(c.computes.key) = ingressCounts(c.computes.key) + 1
          }
        case c : ComputesVar[T] => ()
        case c : ComputesExpr[T] => c.params.foreach(countIngresses(_))
        case c : ComputesFunction[_,_] => countIngresses(c.body)
      }
      countIngresses(computes)
    }
    {
      val visitedSet = HashSet[ComputesKey]()
      val substitutions = HashMap[ComputesKey,Computes[_]]()
      visitedSet += computes.key
      def removeSingletonIndirects[T](computes : Computes[T]) : Computes[T] = {
        implicit val e1 = computes.tType
        computes match {
          case c : Computable[T] => c.replace(c.parts.map(removeSingletonIndirects(_)))
          case c : ComputesIndirect[T] =>
            if !visitedSet(c.computes.key) then {
              visitedSet += c.computes.key
              if ingressCounts(c.computes.key) == 1 then {
                removeSingletonIndirects(c.computes)
              } else {
                substitutions(c.computes.key) = removeSingletonIndirects(c.computes)
                ComputesIndirect(substitutions(c.computes.key).asInstanceOf[Computes[T]])
              }
            } else {
              ComputesIndirect(substitutions(c.computes.key).asInstanceOf[Computes[T]])
            }
          case c : ComputesVar[T] => c
          case c : ComputesExpr[T] => ComputesExpr(c.params.map(removeSingletonIndirects(_)), c.exprFn)
          case c : ComputesFunction[_,_] => c.mapBody(removeSingletonIndirects(_))
        }
      }
      substitutions(computes.key) = removeSingletonIndirects(computes)
      substitutions(computes.key).asInstanceOf[Computes[T]]
    }
  }

  def reifyCall[Arg, Result](computes : Computes[Arg=>Result], arg : Expr[Arg])(implicit reflection: Reflection) = {
    removeRedundantIndirects(computes)
    '{ ??? }
  }

  // problem: even if the input expression is globally reachable, we can't tell here because of how
  // parameters work... user has to re-write this one line anywhere they want to use this
  /* implicit class ComputesFnCallCompiler[Arg, Result](inline computes : Computes[Arg=>Result]) {
    inline def reifyCall(arg : Arg) : Result = ${ reifyCallImpl(computes, '{arg}) }
  } */

}

val add1 : Computes[Int=>Int] =
  (i : Computes[Int]) => ComputesExpr(List(i), es => '{ ${ es(0).asInstanceOf[Expr[Int]] } + 1 })

inline def doAdd1(i : Int) : Int = ${ Computes.reifyCall(add1, '{i}) }

