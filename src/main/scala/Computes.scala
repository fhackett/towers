package towers.computes

import Predef.{any2stringadd => _, _} // allow implicits to override +

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}

import quoted._
import tasty._

type ComputesKey = Int
val NoKey = -1

trait KeySrc {
  def freshKey() : ComputesKey
}

sealed abstract class Computes[T : Type] {
  val tType = implicitly[Type[T]]

  private[computes] var key_ = NoKey
  private[computes] var auxKey_ = NoKey
  def key(implicit keySrc : KeySrc) = {
    if key_ == NoKey then {
      key_ = keySrc.freshKey()
    }
    key_
  }
  def auxKey(implicit keySrc : KeySrc) = {
    if auxKey_ == NoKey then {
      auxKey_ = keySrc.freshKey()
    }
    auxKey_
  }
  val auxVar : ComputesVar[T]

  // we use object identity, so sometimes we need an identical but different object
  def shallowClone : Computes[T]

  // mutable Product - used internally
  def setComputesElement(n : Int, v : Computes[_]) : Unit
  def getComputesElement(n : Int) : Computes[_]
  def computesArity : Int

  def computesIterator : Iterator[Computes[_]] = new scala.collection.AbstractIterator {
    private var c = 0
    private val cmax = computesArity
    override def hasNext = c < cmax
    override def next() = {
      val result = getComputesElement(c)
      c += 1
      result
    }
  }

  // attempt to re-write this Computable (and contents) into something that is somehow "better"
  // by pattern-matching subterms
  def implTryFold(implicit keySrc : KeySrc) : Option[Computes[T]] = tryFold
  def tryFold : Option[Computes[T]]
}

abstract class Computable[T : Type] extends Computes[T] {
  // translate this Computable into some lower-level implementation
  def flatten : Computes[T]

  val auxVar = ComputesVar[T]()

  //val foldUnderstands : List[ClassTag[Computes[T]]]
  //val flattenProduces : ClassTag[Computes[T]]
}

class ComputesVar[T : Type]() extends Computes[T] {
  val auxVar = this
  override def shallowClone = ???
  override def setComputesElement(n : Int, v : Computes[_]) = throw IndexOutOfBoundsException(n.toString)
  override def getComputesElement(n : Int) = throw IndexOutOfBoundsException(n.toString)
  override def computesArity = 0
  override def tryFold = None
}

class ComputesByKey[T : Type](var binding : Computes[T]) extends Computes[T] {
  val auxVar = ComputesVar[T]()
  override def shallowClone = ???
  override def setComputesElement(n : Int, v : Computes[_]) = throw IndexOutOfBoundsException(n.toString)
  override def getComputesElement(n : Int) = throw IndexOutOfBoundsException(n.toString)
  override def computesArity = 0
  override def tryFold = None
}

final class ComputesBinding[V, T : Type](var name : ComputesVar[V], var value : Computes[V], var body : Computes[T]) extends Computes[T] {
  val auxVar = ComputesVar[T]()
  override def shallowClone = ComputesBinding(name, value, body)
  override def setComputesElement(n : Int, v : Computes[_]) = n match {
    case 0 => value = v.asInstanceOf[Computes[V]]
    case 1 => body = v.asInstanceOf[Computes[T]]
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  override def getComputesElement(n : Int) = n match {
    case 0 => value
    case 1 => body
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  override def computesArity = 2
  override def tryFold = None
}

class ComputesExpr[T : Type](var parameters : List[Computes[_]], val exprFn : List[Expr[_]] => Expr[T]) extends Computes[T] {
  val auxVar = ComputesVar[T]()
  override def shallowClone = ComputesExpr(parameters, exprFn)
  override def setComputesElement(n : Int, v : Computes[_]) = parameters = parameters.updated(n, v)
  override def getComputesElement(n : Int) = parameters(n)
  override def computesArity = parameters.length
  override def tryFold = None
}

class ComputesApplication[FnType, Result : Type](var arguments : List[Computes[_]], var function : Computes[FnType]) extends Computes[Result] {
  val auxVar = ComputesVar[Result]()
  override def shallowClone = ComputesApplication(arguments, function)
  override def setComputesElement(n : Int, v : Computes[_]) =
    if n == arguments.length then
      function = v.asInstanceOf[Computes[FnType]]
    else
      arguments = arguments.updated(n, v)
  override def getComputesElement(n : Int) =
    if n == arguments.length then
      function
    else
      arguments(n)
  override def computesArity = arguments.length + 1

  override def implTryFold(implicit keySrc : KeySrc) = function match {
    case fn : ComputesFunction[_,Result] =>
      Some(
        Computes.minSubstituteClone(
          (fn.parameters.map(_.key) zip arguments).toMap,
          fn.body))
    case _ => None
  }
  override def tryFold = ???
}

class ComputesLazyRef[T : Type](ref : =>Computes[T]) extends Computes[T] {
  val auxVar = ComputesVar[T]()
  lazy val computes = ref
  // this node should not survive the initial pass to eliminate it, any attempt to use these signifies catastrophic failure
  override def shallowClone = ???
  override def setComputesElement(n : Int, v : Computes[_]) = ???
  override def getComputesElement(n : Int) = computes.getComputesElement(n)
  override def computesArity = computes.computesArity
  override def tryFold = ???
}

class ComputesFunction[FnType <: Computes.==>[_,Result] : Type, Result : Type](val inst : Computes.FnInst[FnType], val parameters : List[ComputesVar[_]], var body : Computes[Result]) extends Computes[FnType] {
  val auxVar = ComputesVar[FnType]()
  override def shallowClone = ComputesFunction(inst, parameters, body)
  override def setComputesElement(n : Int, v : Computes[_]) = n match {
    case 0 => body = v.asInstanceOf[Computes[Result]]
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  override def getComputesElement(n : Int) = n match {
    case 0 => body
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  override def computesArity = 1
  override def tryFold = None
}

class ComputesSwitch[Arg, Result : Type](
  var argument : Computes[Arg],
  var cases : List[(Computes[Arg],Computes[Result])],
  var default : Option[Computes[Result]]
) extends Computes[Result] {
  val auxVar = ComputesVar[Result]()
  def toList : List[Computes[_]] =
    List(argument) ++ cases.flatMap((tpl : (Computes[Arg],Computes[Result])) => List(tpl._1,tpl._2)) ++ default.map(List(_)).getOrElse(List.empty)
  def fromList(list : List[Computes[_]]) = {
    argument = list.head.asInstanceOf[Computes[Arg]]
    val dExists = list.length % 2 == 0 // list argument, default and some case pairs make an even number (odd without default)
    if dExists then
      default = Some(list.last.asInstanceOf[Computes[Result]])
    else
      default = None
    val cs = if dExists then list.tail.dropRight(1) else list.tail
    cases = (for(List(a,v) <- cs.grouped(2)) yield (a.asInstanceOf[Computes[Arg]], v.asInstanceOf[Computes[Result]])).toList
  }

  override def shallowClone = ComputesSwitch(argument, cases, default)
  override def setComputesElement(n : Int, v : Computes[_]) = fromList(toList.updated(n, v))
  override def getComputesElement(n : Int) = toList(n)
  override def computesArity = toList.length
  override def tryFold = None
}

object Computes {

  class ==>[-Args <: Tuple, +Result](val pc : Int, val closure : Array[Any])

  trait FnInst[F <: (_==>_)] {
    def apply(pc : Expr[Int], closure : Expr[Array[Any]]) : Expr[F]
  }

  implicit def Inst_==>[A <: Tuple,R] : FnInst[A==>R] = new {
    def apply(pc : Expr[Int], closure : Expr[Array[Any]]) = '{ ==>(${ pc }, ${ closure }) }
  }

  type |=>[-Args, +Result] = Tuple1[Args]==>Result

  implicit def freshVar[T : Type] : ComputesVar[T] = ComputesVar[T]()

  def ref[T : Type](computes : =>Computes[T]) : Computes[T] = ComputesLazyRef(computes)

  implicit class ComputesFunction1[
    Arg1 : Type,
    Result : Type,
    F <: Arg1|=>Result : Type](
      fn : Computes[Arg1] => Computes[Result]
    )(implicit
      inst : FnInst[F],
      arg1 : ComputesVar[Arg1]
    ) extends ComputesFunction[F,Result](inst, List(arg1), fn(arg1))

  implicit class ComputesFunction2[
    Arg1 : Type, Arg2 : Type,
    Result : Type,
    F <: (Arg1,Arg2)==>Result : Type](
      fn : (Computes[Arg1], Computes[Arg2]) => Computes[Result]
    )(implicit
      inst : FnInst[F],
      arg1 : ComputesVar[Arg1],
      arg2 : ComputesVar[Arg2]
    ) extends ComputesFunction[F,Result](inst, List(arg1, arg2), fn(arg1, arg2))

  implicit class ComputesFunction3[
    Arg1 : Type, Arg2 : Type, Arg3 : Type,
    Result : Type,
    F <: (Arg1,Arg2,Arg3)==>Result : Type](
      fn : (Computes[Arg1], Computes[Arg2], Computes[Arg3]) => Computes[Result]
    )(implicit
      inst : FnInst[F],
      arg1 : ComputesVar[Arg1],
      arg2 : ComputesVar[Arg2],
      arg3 : ComputesVar[Arg3]
    ) extends ComputesFunction[F,Result](inst, List(arg1, arg2, arg3), fn(arg1, arg2, arg3))

  implicit class ComputesFunction4[
    Arg1 : Type, Arg2 : Type, Arg3 : Type, Arg4 : Type,
    Result : Type,
    F <: (Arg1,Arg2,Arg3,Arg4)==>Result : Type](
      fn : (Computes[Arg1], Computes[Arg2], Computes[Arg3], Computes[Arg4]) => Computes[Result]
    )(implicit
      inst : FnInst[F],
      arg1 : ComputesVar[Arg1],
      arg2 : ComputesVar[Arg2],
      arg3 : ComputesVar[Arg3],
      arg4 : ComputesVar[Arg4]
    ) extends ComputesFunction[F,Result](inst, List(arg1, arg2, arg3, arg4), fn(arg1, arg2, arg3, arg4))

  implicit class ComputesFunction5[
    Arg1 : Type, Arg2 : Type, Arg3 : Type, Arg4 : Type, Arg5 : Type,
    Result : Type,
    F <: (Arg1,Arg2,Arg3,Arg4,Arg5)==>Result : Type](
      fn : (Computes[Arg1], Computes[Arg2], Computes[Arg3], Computes[Arg4], Computes[Arg5]) => Computes[Result]
    )(implicit
      inst : FnInst[F],
      arg1 : ComputesVar[Arg1],
      arg2 : ComputesVar[Arg2],
      arg3 : ComputesVar[Arg3],
      arg4 : ComputesVar[Arg4],
      arg5 : ComputesVar[Arg5]
    ) extends ComputesFunction[F,Result](inst, List(arg1, arg2, arg3, arg4, arg5), fn(arg1, arg2, arg3, arg4, arg5))

  implicit class ComputesApplication1[
      Arg1 : Type,
      Result : Type,
      F <: Arg1|=>Result : Type]
      (fn : =>Computes[F]) {
    def apply(arg1 : Computes[Arg1]) : Computes[Result] = ComputesApplication(List(arg1), ref(fn))
  }

  implicit class ComputesApplication2[
      Arg1 : Type, Arg2 : Type,
      Result : Type,
      F <: (Arg1,Arg2)==>Result : Type]
      (fn : =>Computes[F]) {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2]) : Computes[Result] = ComputesApplication(List(arg1, arg2), ref(fn))
  }

  implicit class ComputesApplication3[
      Arg1 : Type, Arg2 : Type, Arg3 : Type,
      Result : Type,
      F <: (Arg1,Arg2,Arg3)==>Result : Type]
      (fn : =>Computes[F]) {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2], arg3 : Computes[Arg3]) : Computes[Result] =
      ComputesApplication(List(arg1, arg2, arg3), ref(fn))
  }

  implicit class ComputesApplication4[
      Arg1 : Type, Arg2 : Type, Arg3 : Type, Arg4 : Type,
      Result : Type,
      F <: (Arg1,Arg2,Arg3,Arg4)==>Result : Type]
      (fn : =>Computes[F]) {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2], arg3 : Computes[Arg3], arg4 : Computes[Arg4]) : Computes[Result] =
      ComputesApplication(List(arg1, arg2, arg3, arg4), ref(fn))
  }

  implicit class ComputesApplication5[
      Arg1 : Type, Arg2 : Type, Arg3 : Type, Arg4 : Type, Arg5 : Type,
      Result : Type,
      F <: (Arg1,Arg2,Arg3,Arg4,Arg5)==>Result : Type]
      (fn : =>Computes[F]) {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2], arg3 : Computes[Arg3], arg4 : Computes[Arg4], arg5 : Computes[Arg5]) : Computes[Result] =
      ComputesApplication(List(arg1, arg2, arg3, arg4, arg5), ref(fn))
  }

  def eliminateLazyRefs[T](computes : Computes[T], vSet : Set[ComputesKey] = Set.empty)(implicit keySrc : KeySrc) : Computes[T] = {
    val visitedSet = HashSet[ComputesKey]()
    visitedSet ++= vSet
    def impl[T](computes : Computes[T]) : Computes[T] = computes match {
      case c : ComputesLazyRef[T] => impl(c.computes)
      case _ =>
        if !visitedSet(computes.key) then {
          visitedSet += computes.key
          for(i <- 0 until computes.computesArity) {
            computes.setComputesElement(i, impl(computes.getComputesElement(i)))
          }
          computes
        } else {
          computes
        }
    }
    impl(computes)
  }

  def clone[T](computes : Computes[T]) : Computes[T] = {
    val substitutions = HashMap[Computes[_],Computes[_]]()

    def impl[T](computes : Computes[T]) : Computes[T] = {
      if computes.key_ != NoKey then {
        computes // this should only be reachable if we're cloning the result of a tryFold
      } else if substitutions.contains(computes) then {
        substitutions(computes).asInstanceOf[Computes[T]]
      } else {
        computes match {
          case c : ComputesVar[T] => {
            val clone = ComputesVar[T]()(c.tType)
            substitutions(computes) = clone
            clone
          }
          case c : ComputesLazyRef[T] => {
            var innerClone : Computes[T] = null
            val clone = ComputesLazyRef[T](innerClone)(c.tType)
            substitutions(computes) = clone
            innerClone = impl(c.computes)
            clone
          }
          case c : ComputesFunction[f,r] => {
            // this whole cast thing works around dotty bug #6758, which gives f incorrect type bounds
            def thunk[F <: _==>r](c : ComputesFunction[F,r]) = {
              val params = c.parameters.map(impl(_))
              val clone = ComputesFunction[F,r](c.inst, params.asInstanceOf[List[ComputesVar[_]]], null)(c.tType, c.body.tType)
              substitutions(computes) = clone
              clone.body = impl(c.body)
              clone
            }
            thunk(c.asInstanceOf[ComputesFunction[_==>r,r]]).asInstanceOf[Computes[T]]
          }
          case c : ComputesBinding[v,T] => {
            val clone = ComputesBinding[v,T](impl(c.name).asInstanceOf[ComputesVar[v]], null, null)(c.tType)
            substitutions(computes) = clone
            clone.value = impl(c.value)
            clone.body = impl(c.body)
            clone
          }
          case c => {
            val clone = computes.shallowClone
            substitutions(computes) = clone
            for(i <- 0 until clone.computesArity) {
              clone.setComputesElement(i, impl(clone.getComputesElement(i)))
            }
            clone
          }
        }
      }
    }
    
    impl(computes)
  }
  
  def minSubstituteClone[T](map : Map[ComputesKey,Computes[_]], computes : Computes[T])(implicit keySrc : KeySrc) : Computes[T] = {
    val bindings = HashMap[ComputesKey,Computes[_]]()
    bindings ++= map
    val shouldClone = HashSet[ComputesKey]()

    def findRequiredClones[T](computes : Computes[T], reachedSet : Set[ComputesKey]) : Unit = {
      val visitedSet = HashSet[ComputesKey]()
      visitedSet ++= reachedSet
      def impl[T](computes : Computes[T]) : Boolean = {
        if visitedSet(computes.key) || shouldClone(computes.key) then {
          shouldClone(computes.key)
        } else {
          visitedSet += computes.key
          val result = computes match {
            case c : ComputesVar[T] =>
              bindings.contains(c.key)
            case c : ComputesByKey[T] =>
              if c.binding != null then {
                impl(c.binding)
              } else {
                false // this means we are called inside a live (!) cycle so cloning can't cross this even if it wants to
              }
            case c : ComputesLazyRef[T] => ???
            case c => c.computesIterator.foldLeft(false)((acc, e) => impl(e) || acc)
          }
          if result then {
            shouldClone += computes.key
          }
          result
        }
      }
      impl(computes)
    }

    findRequiredClones(computes, Set.empty)
    findRequiredClones(computes, Set.empty)
    //println(s"bindings $bindings")
    //println(s"shouldClone $shouldClone")

    val substitutions = HashMap[ComputesKey,Computes[_]]()
    def impl[T](computes : Computes[T]) : Computes[T] = {
      //println(s"subKey ${computes.key} ${computes}")
      if substitutions.contains(computes.key) then {
        substitutions(computes.key).asInstanceOf[Computes[T]]
      } else if !shouldClone(computes.key) then {
        computes
      } else {
        computes match {
          case c : ComputesVar[T] =>
            bindings(c.key).asInstanceOf[Computes[T]]
          case c : ComputesByKey[T] => {
            if c.binding != null then {
              val clone = ComputesByKey[T](null)(c.tType)
              clone.key // ensure key is set
              substitutions(c.key) = clone
              clone.binding = impl(c.binding)
              clone
            } else {
              ??? // do not clone outside of an in-progress cycle. no vars of interest should exist outside the cycle
                  // if we're inlining inside of it
                  // (crash on sight, since these should never be flagged as shouldClone)
            }
          }
          case c : ComputesBinding[a,T] => {
            val clone = ComputesBinding[a,T](ComputesVar[a]()(c.name.tType), c.value, c.body)(c.tType)
            substitutions(c.key) = clone
            bindings(c.name.key) = clone.name
            clone.value = impl(c.value)
            // recalculate any new transitive clones (to clone a binding, clone its bound name)
            findRequiredClones(clone.body, substitutions.keySet.toSet)
            clone.body = impl(c.body)
            clone
          }
          case c : ComputesFunction[T,v] => {
            def thunk[F <: _==>v](c : ComputesFunction[F,v]) = {
              val names = c.parameters.map({
                case p : ComputesVar[t] =>
                  ComputesVar[t]()(p.tType)
              })
              val clone = ComputesFunction[F,v](c.inst, names, c.body)(c.tType, c.body.tType)
              substitutions(c.key) = clone
              bindings ++= (c.parameters zip names).map({
                case (par, name) => (par.key, name)
              })
              // recalculate any new transitive clones (to clone a function, clone its bound names)
              findRequiredClones(clone.body, substitutions.keySet.toSet)
              clone.body = impl(c.body)
              clone
            }
            thunk(c.asInstanceOf[ComputesFunction[_==>v,v]]).asInstanceOf[Computes[T]]
          }
          case c => {
            val clone = c.shallowClone
            substitutions(computes.key) = clone
            for(i <- 0 until clone.computesArity) {
              clone.setComputesElement(i, impl(clone.getComputesElement(i)))
            }
            clone
          }
        }
      }
    }
    impl(computes)
  }

  trait RewriteAction {
    def apply[T](computes : Computes[T], rec : Computes[T]=>Computes[T], reachedSet : Set[ComputesKey]) : Computes[T]
  }

  def rewrite[T](computes : Computes[T], action : RewriteAction)(implicit keySrc : KeySrc) : Computes[T] = {
    val substitutions = HashMap[ComputesKey,Computes[_]]()
    val isRecursive = HashSet[ComputesKey]()

    def impl[T](computes : Computes[T]) : Computes[T] = {
      if substitutions.contains(computes.key) then {
        substitutions(computes.key).asInstanceOf[Computes[T]] match {
          case c : ComputesByKey[T] => {
            if c.binding == null then {
              //println(s"foundRecursive ${computes.key} ${computes} ${c.key}")
              isRecursive += c.key
            }
            c
          }
          case c => c
        }
      } else {
        computes match {
          case c : ComputesByKey[T] => {
            if c.binding != null then { // if binding is null we are in a recursive call that will eventually set binding
              substitutions(computes.key) = c
              c.binding = impl(c.binding)
            }
            c
          }
          case _ => {
            val indirect = ComputesByKey[T](null)(computes.tType)
            substitutions(computes.key) = indirect

            for(i <- 0 until computes.computesArity) {
              computes.setComputesElement(i, impl(computes.getComputesElement(i)))
            }
            val result = action(computes, impl(_), substitutions.keySet.toSet)
            //println(s"actionResult ${computes.key} ${result.key} ${result}")
            if isRecursive(indirect.key) then {
              indirect.binding = result
              substitutions(computes.key) = indirect.binding
              substitutions(indirect.key) = indirect
              indirect
            } else {
              substitutions(computes.key) = result
              result
            }
          }
        }
      }
    }

    impl(computes)
  }

  def performInlining[T](computes : Computes[T])(implicit keySrc : KeySrc) : Computes[T] =
    rewrite(computes, new {
      def apply[T](computes : Computes[T], rec : Computes[T]=>Computes[T], reachedSet : Set[ComputesKey]) : Computes[T] =
        computes.implTryFold match {
          case Some(folded) => rec(eliminateLazyRefs(Computes.clone(folded), reachedSet))
          case None => computes
        }
    })

  def flatten[T](computes : Computes[T])(implicit keySrc : KeySrc) : Computes[T] =
    rewrite(computes, new {
      def apply[T](computes : Computes[T], rec : Computes[T]=>Computes[T], reachedSet : Set[ComputesKey]) : Computes[T] =
        computes match {
          case c : Computable[T] => rec(eliminateLazyRefs(Computes.clone(c.flatten), reachedSet))
          case c => c
        }
    })

  type BasicBlock = (Map[ComputesKey,Int],Map[ComputesKey,Expr[_]],Expr[Any],Expr[Any]=>Expr[Unit], Expr[Int]=>Expr[Unit], Reflection)=>Expr[Unit]
  type Continuation[T] = (Expr[T],Map[ComputesKey,Int],Map[ComputesKey,Expr[_]],Expr[Any],Expr[Any]=>Expr[Unit], Expr[Int]=>Expr[Unit], Reflection)=>Expr[Unit]

  def getBasicBlocks[T](computes : Computes[T])(implicit keySrc : KeySrc) : List[(ComputesKey,BasicBlock)] = {

    def orderedSetMerge(lhs : List[ComputesVar[_]], rhs : List[ComputesVar[_]]) : List[ComputesVar[_]] = {
      val lset = lhs.map(v => v.key).toSet
      lhs ++ rhs.filter(v => !lset(v.key))
    }

    val nodeClosures = HashMap[ComputesKey,List[ComputesVar[_]]]()
    ;{

      def makePass[T](computes : Computes[T]) : Unit = {
        val visitedSet = HashSet[ComputesKey]()
        def impl[T](computes : Computes[T]) : List[ComputesVar[_]] = {
          if visitedSet(computes.key) then {
            nodeClosures.getOrElse(computes.key, Nil)
          } else {
            visitedSet += computes.key
            val result = computes match {
              case c : ComputesByKey[T] => impl(c.binding)
              case c : ComputesVar[T] => List(c)
              case c : ComputesBinding[_,T] =>
                orderedSetMerge(
                  impl(c.value),
                  impl(c.body).filter(v => v.key != c.name.key))
              case c : ComputesFunction[_,T] => {
                val params = c.parameters.map(v => v.key).toSet
                //println(s"PARAMS ${params}")
                impl(c.body).filter(v => !params(v.key))
              }
              case c =>
                c.computesIterator.foldLeft(Nil : List[ComputesVar[_]])((acc, part) =>
                  orderedSetMerge(acc, impl(part)))
            }
            nodeClosures(computes.key) = orderedSetMerge(result, nodeClosures.getOrElse(computes.key, Nil))
            result
          }
        }
        impl(computes)
      }
      // 2 passes : one to follow all the paths, and one to propagate the results from
      // the back-references
      makePass(computes)
      makePass(computes)
    }

    val blocks = ArrayBuffer[(ComputesKey,BasicBlock)]()
    ;{
      val visitedSet = HashSet[ComputesKey]()

      def bindVars(names : List[ComputesVar[_]], values : List[Expr[_]], reflection : Reflection, scope : Map[ComputesKey,Expr[_]]=>Expr[Unit]) : Expr[Unit] = {
        /*import reflection._
        val vMap = HashMap[ComputesKey,Expr[_]]()
        val statements = (names zip values).flatMap({
          case (name : ComputesVar[t], value) => {
            implicit val e1 = name.tType
            val bloodSacrifice = '{
              val bind = ${ value.asInstanceOf[Expr[t]] }
              bind
            }
            bloodSacrifice.unseal match {
              case IsInlined(inl) => inl.body match {
                case IsBlock(b1) => b1.expr match {
                  // idk why there are 2 blocks nested inside each other here, or what that weird type thing does...
                  case IsBlock(b2) => {
                    vMap(name.key) = b2.expr.seal.cast[t]
                    b1.statements ++ b2.statements
                  }
                }
              }
            }
          }
        })
        Block(
          statements,
          scope(vMap.toMap).unseal).seal.cast[Unit]*/
        def doIt(nv : List[(ComputesVar[_],Expr[_])], vMap : Map[ComputesKey,Expr[_]]) : Expr[Unit] = nv match {
          case Nil => scope(vMap)
          case (name : ComputesVar[t], v) :: tl => {
            implicit val e1 = name.tType
            '{
              val bind = ${ v.asInstanceOf[Expr[t]] }
              ${ doIt(tl, vMap + ((name.key, '{ bind }))) }
            }
          }
        }
        doIt(names zip values, Map.empty)
      }

      def pushClosure(values : List[Expr[_]], pushData : Expr[Any]=>Expr[Unit], reflection : Reflection, scope : Expr[Unit]) : Expr[Unit] = {
        import reflection._
        Block(
          values.map(pushData(_).unseal),
          scope.unseal).seal.cast[Unit]
      }

      def bindSequence(seq : List[Computes[_]], closure : List[ComputesVar[_]], singleUse : Boolean, after : BasicBlock) : BasicBlock = {
        val resultClosures = ArrayBuffer[List[ComputesVar[_]]]()
        seq.foldLeft(Nil : List[ComputesVar[_]])((acc, s) => {
          resultClosures += acc
          orderedSetMerge(acc, List(s.auxVar))
        })
        var inClosure = closure
        val (_, result) = (seq zip resultClosures).foldRight((NoKey, after))((ss, acc) => (ss, acc) match {
          case ((s, resultClosure), (next, after)) => {
            //println(s"rc ${s.key} ${s.auxKey} ${resultClosure.map(_.key)} ${closure.map(_.key)}")
            if next != NoKey then {
              inClosure = orderedSetMerge(inClosure, nodeClosures(next))
            }
            val fullClosure = orderedSetMerge(inClosure, resultClosure)
            (s.key, impl(s, fullClosure, (v, pcMap, vMap, popData, pushData, pushPC, reflection) => {
              if !singleUse then {
                implicit val e1 = s.tType
                '{
                  val bind = ${ v }
                  ${ after(pcMap, vMap + ((s.auxVar.key, '{ bind })), popData, pushData, pushPC, reflection) }
                }
              } else {
                after(pcMap, vMap + ((s.auxVar.key, v)), popData, pushData, pushPC, reflection)
              }
            }))
          }
        })
        result
      }

      // if cont is null, just skip that part and leave whatever you were going to pass to it on the data stack
      def impl[T](computes : Computes[T], closure : List[ComputesVar[_]], cont : Continuation[T]) : BasicBlock = {
        //print("CL "); print(computes); print(" "); print(closure); print(" || "); println(nodeClosures(computes.key).map(_.key))
        val result : BasicBlock = computes match {
          case c : ComputesByKey[T] =>
            c.binding match {
              case c : ComputesFunction[_,T] => impl(c, closure, cont)
              case _ => {
                implicit val e1 = c.tType
                if !visitedSet(c.binding.key) then {
                  visitedSet += c.binding.key
                  val body = impl(c.binding, closure, null)
                  val reverseClosure = nodeClosures(c.binding.key).reverse
                  blocks += ((c.binding.key, (pcMap, vMap, popData, pushData, pushPC, reflection) => {
                    bindVars(reverseClosure, reverseClosure.map(v => '{ ${ popData }.asInstanceOf[${ v.tType }] }), reflection, vMap2 => {
                      //print("l clos "); print(vMap ++ vMap2); println(c)
                      body(pcMap, vMap ++ vMap2, popData, pushData, pushPC, reflection)
                    })
                  }))
                }
                if cont != null then {
                  blocks += ((c.auxKey, (pcMap, vMap, popData, pushData, pushPC, reflection) => {
                    val reverseClosure = closure.reverse
                    '{
                      val arg = ${ popData }.asInstanceOf[T]
                      ${
                        bindVars(reverseClosure, reverseClosure.map(v => '{ ${ popData }.asInstanceOf[${ v.tType }] }), reflection, vMap2 => {
                          cont('{ arg }, pcMap, vMap ++ vMap2, popData, pushData, pushPC, reflection)
                        })
                      }
                    }
                  }))
                }
                (pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                  ${
                    //print("l pre "); print(vMap); println(c)
                    if cont != null then {
                      pushClosure(closure.map(v => vMap(v.key)), pushData, reflection, pushPC(pcMap(c.auxKey).toExpr))
                    } else {
                      '{}
                    }
                  }
                  ${
                    pushClosure(
                      nodeClosures(c.binding.key).map(v => vMap(v.key)),
                      pushData, reflection, pushPC(pcMap(c.binding.key).toExpr))
                  }
                }
              }
            }
          case c : ComputesVar[T] => {
            (pcMap, vMap, popData, pushData, pushPC, reflection) => {
              //println(s"v $vMap ${c.key}")
              if cont == null then
                pushData(vMap(c.key))
              else
                cont(vMap(c.key).asInstanceOf[Expr[T]], pcMap, vMap, popData, pushData, pushPC, reflection)
            }
          }
          case c : ComputesApplication[_,T] => {
            implicit val e1 = c.tType
            implicit val e2 = c.function.tType
            if cont != null then {
              val block : (ComputesKey, BasicBlock) = ((c.auxKey, (pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                val ret = ${ popData }.asInstanceOf[T]
                ${
                  val reverseClosure = closure.reverse
                  bindVars(reverseClosure, reverseClosure.map(v => '{ ${ popData }.asInstanceOf[${ v.tType }] }), reflection, vMap2 => {
                    //print("app clos "); print(vMap ++ vMap2); println(c)
                    cont('{ ret }, pcMap, vMap ++ vMap2, popData, pushData, pushPC, reflection)
                  })
                }
              }))
              blocks += block
            }

            // generate arguments right to left in order to accumulate closures from smallest to largest
            var nextArg : BasicBlock = null
            var fullClosure = closure
            c.arguments.foldRight(NoKey)((arg, nextKey) => {
              fullClosure = orderedSetMerge(fullClosure, if nextKey != NoKey then nodeClosures(nextKey) else Nil)
              val narg = nextArg
              nextArg = impl(
                arg,
                fullClosure,
                if nextKey != NoKey then {
                  (argVal, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                    ${
                      //print("arg "); print(vMap); println(arg)
                      pushData(argVal)
                    }
                    ${ narg(pcMap, vMap, popData, pushData, pushPC, reflection) }
                  }
                } else null)
              arg.key
            })

            // include the left-most argument (skipped above as it is not relevant) in fullClosure
            if !c.arguments.isEmpty then {
              fullClosure = orderedSetMerge(fullClosure, nodeClosures(c.arguments.head.key))
            }
            impl(c.function, fullClosure, (fn, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
              // if we have a continuation then push block to return to, else we are a leaf call
              ${
                //println(s"app $vMap ${c.key} ${closure.map(_.key)}")
                if cont != null then {
                  // push locals left to right
                  pushClosure(closure.map(v => vMap(v.key)), pushData, reflection, pushPC(pcMap(c.auxKey).toExpr))
                } else {
                  '{}
                }
              }
              val fnV = ${ fn }.asInstanceOf[==>[_,_]]
              ${ pushPC('{ fnV.pc }) }
              ${ pushData('{ fnV.closure }) }
              ${
                if !c.arguments.isEmpty then
                  nextArg(pcMap, vMap, popData, pushData, pushPC, reflection)
                else
                  '{}
              }
            })
          }
          case c : ComputesFunction[fnType,_] => {
            // lazily generate function body (incl. stack pop and closure extraction)
            if !visitedSet(c.key) then {
              visitedSet += c.key
              val body = impl(c.body, List.empty, null)
              val block : (ComputesKey,BasicBlock) = ((c.body.key, (pcMap, vMap, popData, pushData, pushPC, reflection) => {
                val reverseParams = c.parameters.reverse
                val fClosure = nodeClosures(c.key)
                bindVars(reverseParams, reverseParams.map(p => '{ ${ popData }.asInstanceOf[${ p.tType }] }), reflection, vMap2 => '{
                  val closureVal = ${ popData }.asInstanceOf[Array[Any]]
                  ${
                    //print("fn args "); print(vMap ++ vMap2); println(c)
                    bindVars(
                      fClosure,
                      for((v, i) <- fClosure.zipWithIndex)
                        yield '{ closureVal(${ i.toExpr }).asInstanceOf[${ v.tType }] },
                      reflection,
                      vMap3 => {
                        //print("fn clos "); print(vMap3); println(c)
                        body(pcMap, vMap ++ vMap2 ++ vMap3, popData, pushData, pushPC, reflection)
                      })
                  }
                })
              }))
              blocks += block
            }
            (pcMap, vMap, popData, pushData, pushPC, reflection) => {
              implicit val e1 = c.tType
              //println(s"CLOS ${nodeClosures(c.key).map(_.key)} VV ${vMap}")
              val refs = nodeClosures(c.key).map(v => vMap(v.key))
              val closureExpr : Expr[Array[Any]] = if !refs.isEmpty then
                '{
                  val clos = new Array[Any](${ refs.length.toExpr })
                  ${
                    refs.zipWithIndex.foldLeft('{})((acc, tp) => tp match {
                      case (ref, i) => '{ clos(${ i.toExpr }) = ${ ref }; ${ acc } }
                    })
                  }
                  clos
                }
              else
                '{ null }
              '{
                val fn = ${ c.inst(pcMap(c.body.key).toExpr, closureExpr) }
                ${
                  //print("ffn "); print(vMap); println(c)
                  if cont != null then
                    cont('{ fn }.asInstanceOf[Expr[T]], pcMap, vMap, popData, pushData, pushPC, reflection)
                  else
                    pushData('{ fn })
                }
              }
            }
          }
          case c : ComputesBinding[_,T] => {
            val body = impl(c.body, closure, cont)
            impl(c.value, closure, (value, pcMap, vMap, popData, pushData, pushPC, reflection) => 
              bindVars(List(c.name), List(value), reflection, vMap2 => {
                //print("bind "); print(vMap ++ vMap2); println(c)
                body(pcMap, vMap ++ vMap2, popData, pushData, pushPC, reflection)
              }))
          }
          case c : ComputesSwitch[_,T] => {
            def thunk[AT,T](c : ComputesSwitch[AT,T], cont : Continuation[T]) : BasicBlock = {
              implicit val e1 = c.tType
              implicit val e2 = c.argument.tType

              if cont != null then {
                val block : (ComputesKey, BasicBlock) = ((c.auxKey, (pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                  val ret = ${ popData }.asInstanceOf[T]
                  ${
                    val reverseClosure = closure.reverse
                    bindVars(reverseClosure, reverseClosure.map(v => '{ ${ popData }.asInstanceOf[${ v.tType }] }), reflection, vMap2 => {
                      //print("switch clos "); print(vMap ++ vMap2); println(c)
                      cont('{ ret }, pcMap, vMap ++ vMap2, popData, pushData, pushPC, reflection)
                    })
                  }
                }))
                blocks += block
              }

              val outputs = c.cases.map(c => c._2.key -> impl(c._2, closure, null)).toMap
              val default = c.default.map(impl(_, closure, null))

              // do not include c.argument.auxVar in bodyClosure, since that will mean that argument is inside its own closure
              // (which will fail is enough indirections happen)
              val bodyClosure = c.cases.map(a => nodeClosures(a._2.key)).foldLeft(closure)(orderedSetMerge)
              bindSequence(c.argument :: c.cases.map(_._1), bodyClosure, true,
                (pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                  ${
                    if cont != null then '{
                      ${ pushPC(pcMap(c.auxKey).toExpr) }
                      ${
                        closure.foldLeft('{})((acc, v) => '{
                          ${ acc }
                          ${ pushData(vMap(v.key)) }
                        })
                      }
                    } else {
                      '{}
                    }
                  }
                  ${
                    import reflection._
                    val bloodSacrifice = '{
                      ${ vMap(c.argument.auxVar.key).asInstanceOf[Expr[AT]] } match {
                        case _ => ()
                      }
                    }/*
                    val scrutinee = bloodSacrifice.unseal match {
                      case IsInlined(inl) => inl.body match {
                        case IsMatch(m) => m.scrutinee
                      }
                    }*/
                    Match(
                      vMap(c.argument.auxVar.key).unseal,
                      (for((v,r) <- c.cases)
                        yield {
                          val bloodSacrifice = '{
                            ${ vMap(c.argument.auxVar.key) } match {
                              case x if x == ${ vMap(v.auxVar.key) } =>
                                ${ outputs(r.key)(pcMap, vMap, popData, pushData, pushPC, reflection) }
                            }
                          }
                          // more hack because I can't generate var bindings myself
                          bloodSacrifice.unseal match {
                            case IsInlined(inl) => inl.body match {
                              case IsMatch(m) => m.cases.head
                            }
                          }
                          /*CaseDef(
                            Pattern.Value(vMap(v.auxVar.key).unseal),
                            None,
                            outputs(r.key)(pcMap, vMap, popData, pushData, pushPC, reflection).unseal)*/
                        })
                      ++ default.map(d =>
                          List({
                            // hack: steal default branch from donor match expression
                            val bloodSacrifice = '{
                              ${ vMap(c.argument.auxVar.key) } match {
                                case _ => ${ d(pcMap, vMap, popData, pushData, pushPC, reflection) }
                              }
                            }
                            bloodSacrifice.unseal match {
                              case IsInlined(inl) => inl.body match {
                                case IsMatch(m) => m.cases.head
                              }
                            }
                          })).getOrElse(Nil)).seal.cast[Unit]
                  }
                })
            }
            thunk(c, cont)
          }
          case c : ComputesExpr[T] => {
            implicit val e1 = c.tType

            bindSequence(c.parameters, closure, false,
              (pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                val result = ${ c.exprFn(c.parameters.map(p => vMap(p.auxVar.key))) }
                //println(s"result $result")
                ${
                  if cont != null then {
                    cont('{ result }, pcMap, vMap, popData, pushData, pushPC, reflection)
                  } else {
                    pushData('{ result })
                  }
                }
              })
          }
          case n => {
            println(n)
            ??? // Computable, ComputesLazyRef (both obsolete at this stage of compilation)
          }
        }
        result
      }

      blocks += ((computes.key, impl(computes, Nil, null)))
    }
    blocks.toList
  }

  def printComputes[T](computes : Computes[T]) : Unit = {
    
    val visitedSet = HashSet[ComputesKey]()
    val names = HashMap[ComputesKey,String]()

    var nextName = "a"
    def freshName = {
      val name = nextName
      def makeNext(name : String) : String = if name.length == 0 then {
        "a"
      } else if name.head == 'z' then {
        "a" ++ makeNext(name.tail)
      } else {
        String(Array((name.head + 1).asInstanceOf[Char])) ++ name.tail
      }
      nextName = makeNext(name)
      name
    }

    var indentation = 0

    def impl[T](computes : Computes[T]) : Unit = {
      for(i <- 0 until indentation) {
        print("  ")
      }
      print(s"${computes.key_}; ${computes.auxKey_}; ${computes.auxVar.key_}; ")
      if names.contains(computes.key_) then {
        print("<>"); println(names(computes.key_))
      } else {
        names(computes.key_) = freshName
        print(names(computes.key_)); print(": ")
        computes match {
          case c : ComputesLazyRef[T] => {
            print(c); print(" :: "); println(c.computes)
          }
          case c : ComputesByKey[T] => {
            print(c); println(" >>")
            indentation += 1
            impl(c.binding)
            indentation -= 1
          }
          case c => println(c)
        }
        indentation += 1
        for(c <- computes.computesIterator) {
          impl(c)
        }
        indentation -= 1
      }
    }

    impl(computes)
  }

  def reifyCall[A1 : Type, R : Type](computes : Computes[A1|=>R], a1 : Expr[A1])
                                    (implicit reflection : Reflection) = {
    reify(computes(expr((), _ => a1)))
  }

  def reify[T : Type](computes : Computes[T])(implicit reflection: Reflection) = {
    var keyCounter = 0
    implicit val keySrc : KeySrc = new KeySrc {
      def freshKey() = {
        val key = keyCounter
        keyCounter += 1
        key
      }
    }
    println("RAW")
    //printComputes(computes)
    val cloned = clone(computes)
    println("CLONED")
    //printComputes(cloned)
    val noLazy = eliminateLazyRefs(cloned)
    println("NOLAZY")
    //printComputes(noLazy)
    //val inlinedComputes = performInlining(noLazy)
    //println("INLINE1")
    //printComputes(inlinedComputes)
    val flattenedComputes = flatten(noLazy)
    println("FLATTENED")
    printComputes(flattenedComputes)
    //val inlinedComputes2 = performInlining(flattenedComputes)
    //println("INLINE2")
    //printComputes(inlinedComputes2)

    val rootKey = flattenedComputes.key
    val basicBlocks = getBasicBlocks(flattenedComputes)

    //println(blocks)
    val pcMap = basicBlocks.zipWithIndex.map((block, idx) => (block._1, idx)).toMap
    import reflection._
    val expr = '{
      val pcStack = ArrayStack[Int]()
      val dataStack = ArrayStack[Any]()

      pcStack.push(${ pcMap(rootKey).toExpr })

      while(!pcStack.isEmpty) {
        println(s"d1 $dataStack")
        println(s"pc $pcStack")
        ${
          Match(
            '{ pcStack.pop }.unseal,
            basicBlocks.map({
              case (key,block) =>
                CaseDef(
                  Pattern.Value(Literal(Constant.Int(pcMap(key)))),
                  None,
                  '{
                    def indirect(pcStack : ArrayStack[Int], dataStack : ArrayStack[Any]) =
                      ${ 
                        block(
                          pcMap,
                          Map.empty,
                          '{ dataStack.pop },
                          v => '{ dataStack.push(${ v }) },
                          pc => '{ pcStack.push(${ pc }) },
                          reflection)
                      }
                    indirect(pcStack, dataStack)
                  }.unseal)
            })).seal
        }
      }
      println(s"d2 $dataStack")
      dataStack.pop.asInstanceOf[T]
    }
    printComputes(flattenedComputes)
    println(expr.show) // DEBUG
    expr
  }

  // problem: even if the input expression is globally reachable, we can't tell here because of how
  // parameters work... user has to re-write this one line anywhere they want to use this
  /* implicit class ComputesFnCallCompiler[Arg, Result](inline computes : Computes[Arg=>Result]) {
    inline def reifyCall(arg : Arg) : Result = ${ reifyCallImpl(computes, '{arg}) }
  } */
  
  implicit object LiftableNull extends Liftable[Null] {
    def toExpr(x : Null) = '{ null }
  }

  implicit object LiftableUnit extends Liftable[Unit] {
    def toExpr(x : Unit) = '{ () }
  }
  
  implicit class ComputesIntOps(lhs : Computes[Int]) {
    def +(rhs : Computes[Int]) : Computes[Int] =
      expr((lhs, rhs), t => t match { case (lhs,rhs) => '{ ${ lhs } + ${ rhs } }})
    def -(rhs : Computes[Int]) : Computes[Int] =
      expr((lhs, rhs), t => t match { case (lhs,rhs) => '{ ${ lhs } - ${ rhs } }})
  }

  implicit class ComputesTuple2[T1, T2](tpl : (Computes[T1],Computes[T2])) extends Computable[(T1,T2)]()('[(${ tpl._1.tType },${ tpl._2.tType })]) {
    var tuple = tpl

    override def shallowClone = ComputesTuple2(tuple)

    override def computesArity = 2
    override def getComputesElement(n : Int) : Computes[_] = n match {
      case 0 => tuple._1
      case 1 => tuple._2
      case _ => throw IndexOutOfBoundsException(n.toString)
    }
    override def setComputesElement(n : Int, v : Computes[_]) = n match {
      case 0 => tuple = (v.asInstanceOf[Computes[T1]], tuple._2)
      case 1 => tuple = (tuple._1, v.asInstanceOf[Computes[T2]])
      case _ => throw IndexOutOfBoundsException(n.toString)
    }

    override def tryFold = None
    override def flatten = {
      implicit val e1 = tuple._1.tType
      implicit val e2 = tuple._2.tType
      ComputesExpr(List(tuple._1, tuple._2), ex => '{ (${ ex(0).asInstanceOf[Expr[T1]] }, ${ ex(1).asInstanceOf[Expr[T2]] }) })
      //expr(tuple : (Computes[T1],Computes[T2]), (etpl : (Expr[T1],Expr[T2])) => '{ (${ etpl._1 }, ${ etpl._2 }) })
    }
  }

  implicit class ComputesTuple2Ops[T1 : Type, T2 : Type](lhs : Computes[(T1,T2)]) {
    def _1 : Computes[T1] =
      expr(lhs, lhs => '{ ${ lhs }._1 })
    def _2 : Computes[T2] =
      expr(lhs, lhs => '{ ${ lhs }._2 })
  }

  implicit class ComputesListOps[T : Type](lhs : Computes[List[T]]) {
    def isEmpty : Computes[Boolean] =
      expr(lhs, lhs => '{ ${ lhs }.isEmpty })
    def head : Computes[T] =
      expr(lhs, lhs => '{ ${ lhs }.head })
    def tail : Computes[List[T]] =
      expr(lhs, lhs => '{ ${ lhs }.tail })
  }

  implicit class ComputesSwitchOp[Lhs](lhs : Computes[Lhs]) {
    def switch[Rhs : Type](cases : List[(Computes[Lhs],Computes[Rhs])], default : Computes[Rhs]) : Computes[Rhs] =
      ComputesSwitch(lhs, cases, Some(default))
    def switch[Rhs : Type](cases : List[(Computes[Lhs],Computes[Rhs])]) : Computes[Rhs] =
      ComputesSwitch(lhs, cases, None)
  }

  def let[V : Type,T : Type](value : Computes[V], body : Computes[V|=>T]) : Computes[T] = body(value)

  def const[T : Type : Liftable](v : T) : Computes[T] =
    ComputesExpr(Nil, es => v.toExpr)

  type ComputesToExpr[C <: Tuple] <: Tuple = C match {
    case Unit => Unit
    case Computes[t] *: tl => Expr[t] *: ComputesToExpr[tl]
  }

  def expr[T : Type, Param](param : Computes[Param], body : Expr[Param] => Expr[T]) : Computes[T] =
    ComputesExpr(
      List(param),
      exprs => body(exprs.head.asInstanceOf[Expr[Param]]))

  def expr[T : Type, Params <: Tuple](params : Params, body : ComputesToExpr[Params] => Expr[T]) : Computes[T] =
    ComputesExpr(
      params.toArray.toList.asInstanceOf[List[Computes[_]]],
      exprs => body(exprs.foldRight(() : Tuple)((hd, tl) => hd *: tl).asInstanceOf[ComputesToExpr[Params]]))

}

import Computes._

val add1 : Computes[Int|=>Int] =
  (i : Computes[Int]) => i+const(1)

val add2 : Computes[Int|=>Int] =
  (i : Computes[Int]) => add1(add1(i))

val countdown : Computes[Int|=>Boolean] =
  (i : Computes[Int]) =>
    i.switch(
      List(const(0) -> const(true)),
      default=countdown(i-const(1)))

val add1AddedL : Computes[Int|=>Int] =
  (i : Computes[Int]) =>
    i + add1(i)

val add1AddedR : Computes[Int|=>Int] =
  (i : Computes[Int]) =>
    add1(i) + i

val unimap : Computes[(List[Int],Int|=>Int)==>List[Int]] =
  (list : Computes[List[Int]], fn : Computes[Int|=>Int]) =>
    list.isEmpty.switch(
      List(
        const(true) -> expr((), _ => '{ Nil }),
        const(false) ->
          expr((fn(list.head), unimap(list.tail, fn)),
            tpl => tpl match { case (mhd,mtl) => '{ ${ mhd } :: ${ mtl } } })))

val unimap2 : Computes[(List[Int],Int|=>Int)|=>List[Int]] =
  (args : Computes[(List[Int],Int|=>Int)]) =>
    let(expr(args, args => '{ ${ args }._1 }),
      (list : Computes[List[Int]]) =>
        let(expr(args, args => '{ ${ args }._2 }),
          (fn : Computes[Int|=>Int]) =>
            list.isEmpty.switch(
              List(
                const(true) -> expr((), _ => '{ Nil }),
                const(false) ->
                  expr((fn(list.head), unimap2((list.tail, fn))),
                    tpl => tpl match { case (mhd,mtl) => '{ ${ mhd } :: ${ mtl } } })))))

val unimapAdd1 : Computes[List[Int]|=>List[Int]] =
  (list : Computes[List[Int]]) =>
    unimap(list, add1)

val unimap2Add1 : Computes[List[Int]|=>List[Int]] =
  (list : Computes[List[Int]]) =>
    unimap2((list, add1))

inline def doAdd1(i : Int) : Int = ${ Computes.reifyCall(add1, '{ i }) }

inline def doAdd2(i : Int) : Int = ${ Computes.reifyCall(add2, '{ i }) }

inline def doCountdown(i : Int) : Boolean = ${ Computes.reifyCall(countdown, '{ i }) }

inline def doAdd1AddedL(i : Int) : Int = ${ Computes.reifyCall(add1AddedL, '{ i }) }

inline def doAdd1AddedR(i : Int) : Int = ${ Computes.reifyCall(add1AddedR, '{ i }) }

inline def doUnimapAdd1(list : List[Int]) : List[Int] = ${ Computes.reifyCall(unimapAdd1, '{ list }) }

inline def doUnimap2Add1(list : List[Int]) : List[Int] = ${ Computes.reifyCall(unimap2Add1, '{ list }) }

