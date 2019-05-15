package towers.computes

import scala.collection.mutable.{HashMap, HashSet, ArrayStack}

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

class ComputesVar[T : Type]() extends Computes[T] {
  var binding : Option[Computes[T]] = None // this simulates let-bindings without introducing any AST nodes for them
                                           // why? so the optimisers are not affected by how many/few let-bindings
                                           // are generated.
                                           // let-bindings can obscure AST structure "high" up the AST without really adding anything
                                           // but this is guaranteed to cause no more disruption than 2 or more Var nodes
                                           // that we can't inline, keeping all other structure intact
}

// you will never see this outside of final stages of compilation - generally all bindings are hidden inside the Var nodes
class ComputesBinding[V, T : Type](val name : ComputesVar[V], val value : Computes[V], val body : Computes[T]) extends Computes[T]

class ComputesExpr[T : Type](val params : List[Computes[_]], val exprFn : List[Expr[_]] => Expr[T]) extends Computes[T]

class ComputesApply[Arg, Result : Type](val argument : Computes[Arg], fn : =>Computes[Arg=>Result]) extends Computes[Result] {
  lazy val function = fn
}

class ComputesSwitch[Arg, Result : Type](val argument : Computes[Arg], val cases : List[(Computes[Arg],Computes[Result])],
  val default : Option[Computes[Result]]) extends Computes[Result]

sealed abstract class VMAction
case class CallAction(val dest : Int, val arg : Any) extends VMAction
case class ReturnAction(val ret : Any) extends VMAction
case class PushRetAction(val pushed : (Int,Tuple), val next : VMAction) extends VMAction

object Computes {

  implicit class ComputesFunction[Arg : Type, Result : Type](fn : Computes[Arg] => Computes[Result]) extends Computes[Arg=>Result] {
    var arg = ComputesVar[Arg]() // mutable, or we can't implement mapBody
    val body : Computes[Result] = fn(arg)

    def mapBody(fn : Computes[Result] => Computes[Result]) : ComputesFunction[Arg,Result] = {
      val mapped = ComputesFunction[Arg,Result](_ => fn(body))
      mapped.arg = arg
      mapped
    }
  }

  implicit class ComputesApplicationOp[Arg : Type,Result : Type](fn : =>Computes[Arg=>Result]) {
    def apply(arg : Computes[Arg]) : Computes[Result] = ComputesApply(arg, fn)
  }

  def removeRedundantIndirects[T](computes : Computes[T]) : Computes[T] = {
    val ingressCounts = HashMap[ComputesKey,Int]();
    {
      val visitedSet = HashSet[ComputesKey]()
      visitedSet += computes.key
      ingressCounts(computes.key) = 1
      def countIngresses[T](computes : Computes[T]) : Unit = computes match {
        case c : Computable[T] => c.parts.foreach(countIngresses(_))
        case c : ComputesVar[T] => {
          if !visitedSet(c.key) then {
            visitedSet += c.key
            ingressCounts(c.key) = 1
            c.binding.foreach(countIngresses(_))
          } else {
            ingressCounts(c.key) += 1
          }
        }
        case c : ComputesBinding[_,_] => ???
        case c : ComputesExpr[T] => c.params.foreach(countIngresses(_))
        case c : ComputesApply[_,T] => {
          countIngresses(c.argument)
          if !visitedSet(c.function.key) then {
            visitedSet += c.function.key
            ingressCounts(c.function.key) = 1
            countIngresses(c.function)
          } else {
            ingressCounts(c.function.key) += 1
          }
        }
        case c : ComputesSwitch[_,T] => {
          countIngresses(c.argument)
          for((v, r) <- c.cases) {
            countIngresses(v)
            countIngresses(r)
          }
          c.default.foreach(countIngresses(_))
        }
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
          case c : ComputesVar[T] =>
            // if a bound variable is used exactly once, we can substitute it with the AST for its value
            // this is the simplest useful but strictly correct strategy I could find.
            // we could be "smarter", like "small constants can be substituted" or something, but are not
            // right now
            // note: as below, we check substitution before we check if we've seen this var before since
            // beta reduction adds a new binding and reruns this code
            if ingressCounts(c.key) == 1 && !c.binding.isEmpty then {
              val sub = if !visitedSet(c.key) then {
                removeSingletonIndirects(c.binding.get)
              } else {
                c.binding.get
              }
              substitutions(c.key) = sub
              sub
            } else {
              if !visitedSet(c.key) then {
                visitedSet += c.key
                c.binding = c.binding.map(removeSingletonIndirects(_))
                substitutions(c.key) = c
              }
              c
            }
          case c : ComputesBinding[_,_] => ???
          case c : ComputesExpr[T] => ComputesExpr(c.params.map(removeSingletonIndirects(_)), c.exprFn)
          case c : ComputesApply[_,T] => {
            val arg = removeSingletonIndirects(c.argument)
            if ingressCounts(c.function.key) == 1 then {
              val fn = removeSingletonIndirects(c.function)
              // try to perform beta reduction
              fn match {
                case cc : ComputesFunction[c.argument.T,T] => {
                  // binds the argument then looks for any further opportunities in the body
                  // now that we know what the argument is (this is why it this code is written
                  // like it's ok to process the same node twice - the body will be visited twice or more)
                  cc.arg.binding = Some(arg)
                  removeSingletonIndirects(cc.body)
                }
                case _ => ComputesApply(arg, fn) // reaching this means we don't know the function body
                                                 // give up for now, maybe it will be bound later
              }
            } else {
              if !visitedSet(c.function.key) then {
                visitedSet += c.function.key
                val sub = removeSingletonIndirects(c.function)
                substitutions(c.function.key) = sub
                ComputesApply(arg, sub)
              } else {
                ComputesApply(arg, substitutions(c.function.key).asInstanceOf[Computes[c.argument.T=>T]])
              }
            }
          }
          case c : ComputesSwitch[_,T] => {
            ComputesSwitch(
              removeSingletonIndirects(c.argument),
              for((v, r) <- c.cases)
                yield (removeSingletonIndirects(v), removeSingletonIndirects(r)),
              c.default.map(removeSingletonIndirects(_)))
          }
          case c : ComputesFunction[_,_] => c.mapBody(removeSingletonIndirects(_))
        }
      }
      removeSingletonIndirects(computes)
    }
  }

  def getBlocks[T](computes : Computes[T]) : List[Computes[_]] =
    ???

  def codegenBlock[T](computes : Computes[T], pcMap : Map[ComputesKey,Int]) : Expr[Tuple=>T] = {
    ???
  }

  def reifyCall[Arg : Type, Result : Type](computes : Computes[Arg=>Result], arg : Expr[Arg])
                                          (implicit reflection: Reflection) = {
    removeRedundantIndirects(computes)
    val pcMap = HashMap[ComputesKey,Int]()
    import reflection._
    '{
      val stack = ArrayStack[(Int,Tuple)]()
      var reg : Any = ${ arg }
      var iterate = true
      var pc : Int = ${ pcMap(computes.key).toExpr }
      do {
        ${
          ???
        };
      } while(iterate);
      reg.asInstanceOf[Result]
    }
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

