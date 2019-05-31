package towers.computes

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}

import quoted._
import tasty._

class ComputesKey()

sealed abstract class Computes[Tp : Type] {
  type T = Tp
  val tType = implicitly[Type[T]]
  val key = ComputesKey()

  // we use object identity, so sometimes we need an identical but different object
  def shallowClone : Computes[Tp]

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

  def +[T2,Out](rhs : Computes[T2])(implicit ev : Computes.OverridesPlus[Tp,T2,Out]) : Computes[Out] = ev.+(this, rhs)

  // attempt to re-write this Computable (and contents) into something that is somehow "better"
  // by pattern-matching subterms
  def tryFold : Option[Computes[T]]
}

abstract class Computable[T : Type] extends Computes[T] {
  // translate this Computable into some lower-level implementation
  def flatten : Computes[T]

  //val foldUnderstands : List[ClassTag[Computes[T]]]
  //val flattenProduces : ClassTag[Computes[T]]
}

class ComputesVar[T : Type]() extends Computes[T] {
  override def shallowClone = ???
  override def setComputesElement(n : Int, v : Computes[_]) = throw IndexOutOfBoundsException(n.toString)
  override def getComputesElement(n : Int) = throw IndexOutOfBoundsException(n.toString)
  override def computesArity = 0
  override def tryFold = None
}

class ComputesByKey[T : Type](val link : ComputesKey) extends Computes[T] {
  override def shallowClone = ???
  override def setComputesElement(n : Int, v : Computes[_]) = throw IndexOutOfBoundsException(n.toString)
  override def getComputesElement(n : Int) = throw IndexOutOfBoundsException(n.toString)
  override def computesArity = 0
  override def tryFold = None
}

final class ComputesBinding[V, T : Type](var name : ComputesVar[V], var value : Computes[V], var body : Computes[T]) extends Computes[T] {
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
  override def shallowClone = ComputesExpr(parameters, exprFn)
  override def setComputesElement(n : Int, v : Computes[_]) = parameters = parameters.updated(n, v)
  override def getComputesElement(n : Int) = parameters(n)
  override def computesArity = parameters.length
  override def tryFold = None
}

class ComputesApplication[FnType, Result : Type](var arguments : List[Computes[_]], var function : Computes[FnType]) extends Computes[Result] {
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

  override def tryFold = function match {
    case fn : ComputesFunction[_,Result] =>
      Some(
        Computes.substitute(
          (fn.parameters.map(_.key) zip arguments).toMap,
          Computes.clone(fn.body)))
    case _ => None
  }
}

class ComputesLazyRef[T : Type](ref : =>Computes[T]) extends Computes[T] {
  lazy val computes = ref
  // this node should not survive the initial pass to eliminate it, and it's essentially impossible to implement these for it anyway
  override def shallowClone = ???
  override def setComputesElement(n : Int, v : Computes[_]) = ???
  override def getComputesElement(n : Int) = ???
  override def computesArity = ???
  override def tryFold = ???
}

class ComputesFunction[FnType : Type, Result : Type](val parameters : List[ComputesVar[_]], var body : Computes[Result]) extends Computes[FnType] {
  override def shallowClone = ComputesFunction(parameters, body) // TODO: renaming
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

  implicit def freshVar[T : Type] : ComputesVar[T] = ComputesVar[T]()

  def ref[T : Type](computes : =>Computes[T]) : Computes[T] = ComputesLazyRef(computes)

  implicit class ComputesFunction1[
    Arg1 : Type,
    Result : Type](
      fn : Computes[Arg1] => Computes[Result]
    )(implicit
      arg1 : ComputesVar[Arg1]
    ) extends ComputesFunction[Arg1=>Result,Result](List(arg1), fn(arg1))

  implicit class ComputesFunction2[
    Arg1 : Type, Arg2 : Type,
    Result : Type](
      fn : (Computes[Arg1], Computes[Arg2]) => Computes[Result]
    )(implicit
      arg1 : ComputesVar[Arg1],
      arg2 : ComputesVar[Arg2]
    ) extends ComputesFunction[(Arg1,Arg2)=>Result,Result](List(arg1, arg2), fn(arg1, arg2))

  implicit class ComputesFunction3[
    Arg1 : Type, Arg2 : Type, Arg3 : Type,
    Result : Type](
      fn : (Computes[Arg1], Computes[Arg2], Computes[Arg3]) => Computes[Result]
    )(implicit
      arg1 : ComputesVar[Arg1],
      arg2 : ComputesVar[Arg2],
      arg3 : ComputesVar[Arg3]
    ) extends ComputesFunction[(Arg1,Arg2,Arg3)=>Result,Result](List(arg1, arg2, arg3), fn(arg1, arg2, arg3))

  implicit class ComputesApplication1[Arg1 : Type, Result : Type](fn : =>Computes[Arg1=>Result]) {
    def apply(arg1 : Computes[Arg1]) : Computes[Result] = ComputesApplication(List(arg1), ref(fn))
  }

  implicit class ComputesApplication2[Arg1 : Type, Arg2 : Type, Result : Type](fn : =>Computes[(Arg1,Arg2)=>Result]) {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2]) : Computes[Result] = ComputesApplication(List(arg1, arg2), ref(fn))
  }

  implicit class ComputesApplication3[Arg1 : Type, Arg2 : Type, Arg3 : Type, Result : Type](fn : =>Computes[(Arg1,Arg2,Arg3)=>Result]) {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2], arg3 : Computes[Arg3]) : Computes[Result] =
      ComputesApplication(List(arg1, arg2, arg3), ref(fn))
  }

  trait OverridesPlus[Lhs,Rhs,Out] {
    def +(lhs : Computes[Lhs], rhs : Computes[Rhs]) : Computes[Out]
  }

  def addIndirect(key : ComputesKey, parent : Computes[_], indirects : HashMap[ComputesKey,ArrayBuffer[Computes[_]]]) : Unit = {
    var buf = indirects.getOrElseUpdate(key, ArrayBuffer())
    buf += parent
  }

  def fixIndirects(key : ComputesKey, patch : Computes[_], indirects : HashMap[ComputesKey,ArrayBuffer[Computes[_]]]) : Unit = {
    if indirects.contains(key) then {
      for(parent <- indirects(key);
          i <- 0 until parent.computesArity) {
        parent.getComputesElement(i) match {
          case c : ComputesByKey[_] if c.link == key =>
            parent.setComputesElement(i, patch)
          case _ => ()
        }
      }
      indirects -= key
    }
  }

  def eliminateLazyRefs[T](computes : Computes[T]) : Computes[T] = {
    val substitutions = HashMap[ComputesKey,Computes[_]]()
    val indirects = HashMap[ComputesKey,ArrayBuffer[Computes[_]]]()

    def impl[T](computes : Computes[T], parent : Computes[_]) : Computes[T] = {
      if substitutions.contains(computes.key) then {
        val sub = substitutions(computes.key)
        if sub == null then {
          implicit val e1 = computes.tType
          addIndirect(computes.key, parent, indirects)
          ComputesByKey(computes.key)
        } else {
          sub.asInstanceOf[Computes[T]]
        }
      } else {
        substitutions(computes.key) = null
        val result = computes match {
          case lz : ComputesLazyRef[T] =>
            impl(lz.computes, parent)
          case _ => {
            for(i <- 0 until computes.computesArity) {
              computes.setComputesElement(i, impl(computes.getComputesElement(i), computes))
            }
            computes
          }
        }
        substitutions(computes.key) = result
        fixIndirects(computes.key, result, indirects)
        result
      }
    }
    impl(computes, null)
  }

  def clone[T](computes : Computes[T]) : Computes[T] = computes match {
    case c : ComputesVar[T] => c
    case c : ComputesByKey[T] => c
    case _ => {
      val shallow = computes.shallowClone
      for(i <- 0 until shallow.computesArity) {
        shallow.setComputesElement(i, clone(shallow.getComputesElement(i)))
      }
      shallow
    }
  }
  
  def substitute[T](map : Map[ComputesKey,Computes[_]], computes : Computes[T]) : Computes[T] = computes match {
    case c : ComputesVar[T] =>
      if map.contains(c.key) then map(c.key).asInstanceOf[Computes[T]] else c
    case _ => {
      for(i <- 0 until computes.computesArity) {
        computes.setComputesElement(i, substitute(map, computes.getComputesElement(i)))
      }
      computes
    }
  }

  def performInlining[T](computes : Computes[T]) : Computes[T] = {
    val substitutions = HashMap[ComputesKey,Computes[_]]()
    val indirects = HashMap[ComputesKey,ArrayBuffer[Computes[_]]]()
    val isRecursive = HashSet[ComputesKey]()

    def findRecursive[T](computes : Computes[T], reachableFrom : Set[ComputesKey]) : Unit =
      if isRecursive(computes.key) then {
        ()
      } else if reachableFrom(computes.key) then {
        isRecursive += computes.key
      } else {
        val reachableFrom2 = reachableFrom + computes.key
        for(i <- 0 until computes.computesArity) {
          findRecursive(computes.getComputesElement(i), reachableFrom2)
        }
      }

    def impl[T](computes : Computes[T], parent : Computes[_]) : Computes[T] = {
      if substitutions.contains(computes.key) then {
        val sub = substitutions(computes.key)
        if sub == null then {
          implicit val e1 = computes.tType
          addIndirect(computes.key, parent, indirects)
          ComputesByKey(computes.key)
        } else {
          sub.asInstanceOf[Computes[T]]
        }
      } else {
        substitutions(computes.key) = null
        for(i <- 0 until computes.computesArity) {
          computes.setComputesElement(i, impl(computes.getComputesElement(i), computes))
        }
        val result = if isRecursive(computes.key) then {
          computes // don't fold if a node contains itself (though you might have folded something locally inside the node)
        } else {
          computes.tryFold match {
            case Some(folded) => {
              val f2 = eliminateLazyRefs(folded)
              findRecursive(f2, Set.empty) // folds may somehow introduce local recursions we didn't know about
              // recurse on fold result in case the result of the fold needs any inlining
              // (this will ignore anything the fold didn't touch because the key will already be in substitutions)
              impl(f2, parent)
            }
            case None => computes
          }
        }
        substitutions(computes.key) = result
        fixIndirects(computes.key, result, indirects)
        result
      }
    }

    findRecursive(computes, Set.empty)
    impl(computes, null)
  }

  def flatten[T](computes : Computes[T]) : Computes[T] = {
    val substitutions = HashMap[ComputesKey,Computes[_]]()
    val indirects = HashMap[ComputesKey,ArrayBuffer[Computes[_]]]()

    def impl[T](computes : Computes[T], parent : Computes[_]) : Computes[T] = {
      if substitutions.contains(computes.key) then {
        val sub = substitutions(computes.key)
        if sub == null then {
          implicit val e1 = computes.tType
          addIndirect(computes.key, parent, indirects)
          ComputesByKey(computes.key)
        } else {
          sub.asInstanceOf[Computes[T]]
        }
      } else {
        substitutions(computes.key) = null
        for(i <- 0 until computes.computesArity) {
          computes.setComputesElement(i, impl(computes.getComputesElement(i), computes))
        }
        val result = computes match {
          case c : Computable[T] => {
            val flat = eliminateLazyRefs(c.flatten)
            val inlined = performInlining(flat)
            impl(inlined, parent)
          }
          case _ => computes
        }
        substitutions(computes.key) = result
        fixIndirects(computes.key, result, indirects)
        result
      }
    }

    impl(computes, null)
  }

  /*def inferBindings[T](computes : Computes[T]) : Computes[T] = {
    val mentionCounts = HashMap[ComputesKey, Int]()
    ;{
      val visitedSet = HashSet[ComputesKey]()
      def countMentions[T](computes : Computes[T]) : Unit = computes match {
        case c : Computable[T] => ???
        case c : ComputesVar[T] =>
          if !c.binding.isEmpty then {
            if mentionCounts.contains(c.key) then {
              mentionCounts(c.key) = 1
            } else {
              mentionCounts(c.key) += 1
            }
          }
        case c : ComputesBinding[_,T] => ???
        case c : ComputesExpr[T] => c.params.foreach(countMentions(_))
        case c : ComputesApply[_,T] => {
          if !visitedSet(c.function.key) then {
            visitedSet += c.function.key
            countMentions(c.argument)
            countMentions(c.function)
          } else {
            countMentions(c.argument)
          }
        }
        case c : ComputesSwitch[_,T] => {
          countMentions(c.argument)
          for((v,r) <- c.cases) {
            countMentions(v)
            countMentions(r)
          }
          c.default.foreach(countMentions(_))
        }
        case c : ComputesFunction[_,_] => countMentions(c.body)
      }
    }
    val visitedSet = HashSet[ComputesKey]()
    var foundCounts : Map[ComputesKey,Int] = Map.empty
    var bindQueue = ArrayBuffer[ComputesVar[_]]()
    val substitutions = HashMap[ComputesKey, Computes[_]]()
    def impl[T](computes : Computes[T]) : Computes[T] = {
      implicit val e1 = computes.tType
      val oldBindQueue = bindQueue
      val oldFoundCounts = foundCounts
      bindQueue = ArrayBuffer[ComputesVar[_]]()
      var result : Computes[T] = computes match {
        case c : Computable[T] => ???
        case c : ComputesVar[T] => {
          if !c.binding.isEmpty then {
            foundCounts = foundCounts + ((c.key, foundCounts.getOrElse(c.key, 0) + 1))
            if foundCounts(c.key) == mentionCounts(c.key) then {
              bindQueue += c
            }
          }
          c
        }
        case c : ComputesBinding[_,T] => ???
        case c : ComputesExpr[T] => ComputesExpr(c.params.map(impl(_)), c.exprFn)
        case c : ComputesApply[_,T] =>
          if visitedSet(c.function.key) then {
            ComputesApply(impl(c.argument), substitutions(c.function.key).asInstanceOf[Computes[c.argument.T=>T]])
          } else {
            visitedSet += c.function.key
            val sub = impl(c.function)
            substitutions(c.function.key) = sub
            ComputesApply(impl(c.argument), sub)
          }
        case c : ComputesSwitch[_,T] =>
          ComputesSwitch(
            impl(c.argument),
            for((v,r) <- c.cases)
              yield (impl(v), impl(r)),
            c.default.map(impl(_)))
        case c : ComputesFunction[_,_] => c.mapBody(impl(_))
      }
      // bind each var at the lowest point in the tree possible.
      // if a var is in the queue, we just found its last mention
      // if we have heard of it before (in a sibling/cousin), it belongs to one of our parents
      // otherwise, bind it here
      for(v <- bindQueue) {
        if oldFoundCounts(v.key) == 0 then {
          result = ComputesBinding(v, v.binding.get, result)
        } else {
          oldBindQueue += v
        }
      }
      bindQueue = oldBindQueue
      result
    }
    visitedSet += computes.key
    val result = impl(computes)
    substitutions(computes.key) = result
    result
  }*/

  /*def containsApplication[T](computes : Computes[T]) : Boolean = computes match {
        case c : Computable[T] => ???
        case c : ComputesVar[T] => false
        case c : ComputesBinding[_,T] => containsCall(c.value) || containsCall(c.body)
        case c : ComputesExpr[T] => c.params.exists(containsCall(_))
        case c : ComputesApply[_,T] => true
        case c : ComputesSwitch[_,T] =>
          containsCall(c.argument) ||
          c.cases.exists((v, r) => containsCall(v) || containsCall(r)) ||
          c.default.map(containsCall(_)).getOrElse(false)
        case c : ComputesFunction[_,_] => false 
  }

  def complexify[T](computes : Computes[T]) : Computes[T] = {
    val substitutions = HashMap[ComputesKey,Computes[_]]()
    val indirects = HashMap[ComputesKey,ArrayBuffer[Computes[_]]]()

    def impl[T](computes : Computes[T], parent : Computes[_]) : Computes[T] = {
      if substitutions.contains(computes.key) then {
        val sub = substitutions(computes.key)
        if sub == null {
          addIndirect(computes.key, parent, indirects)
          ComputesByKey(computes.key)
        } else {
          sub
        }
      } else {
        substitutions(computes.key) = null
        for(i <- 0 until computes.computesArity) {
          computes.setComputesElement(i, impl(computes.getComputesElement(i), computes))
        }
        val result = computes match {
          case c : Computable[T] => ???
          case c : ComputesExpr[T] if c.parameters.exists(containsApplication(_)) => {
            val args = c.parameters.map(_ => ComputesVar[_]())
            ComputesApplication(c.parameters, ComputesFunction(args, ComputesExpr(args, c.exprFn)))
          }
          case c : ComputesSwitch[_,T] if containsApplication(c.argument) || c.cases.exists(containsApplication(_._1)) => {
            val arg = ComputesVar()
            val caseArgs = c.cases.map(_ => ComputesVar[_]())
            ComputesApplication(
              c.argument :: c.cases.map(_._1),
              ComputesFunction(
                arg :: caseArgs,
                ComputesSwitch(
                  arg,
                  for((ca, (a,v)) <- (caseArgs zip c.cases))
                    yield (ca, v),
                  default=c.default)))
          }
          // if the function you're applying is itself computed as result of some recursion, first compute the function
          // then apply it
          case c : ComputesApplication[_,T] if containsApplication(c.function) => {
            val fn = ComputesVar()
            ComputesApplication(
              List(c.function),
              ComputesFunction(
                List(fn),
                ComputesApplication(c.arguments, fn)))
          }
          case c : ComputesBinding[_,T] if containsApplication(c.value) => {
            ComputesApplication(List(c.value), ComputesFunction(List(c.name), c.body))
          }
          case _ => computes
        }
        substitutions(computes.key) = result
        fixIndirects(computes.key, result, indirects)
        result
      }
    }

    impl(computes)
  }

  def getBlocks[T](computes : Computes[T]) : List[Computes[_]] = {
    val visitedSet = HashSet[ComputesKey]()
    val blocks = ArrayBuffer[ComputesFunction[_,_]]()
    def impl[T](computes : Computes[T]) : Unit = {
      if visitedSet(computes.key) then {
        ()
      } else {
        visitedSet += computes.key
        computes match {
          c : ComputesFunction[_,_] =>
            blocks += c
          c : ComputesExpr[T] => {
            var needsBlock = false
            for(param <- c.parameters) {
              if needsBlock then {
                blocks += param
              } else if containsApplication then {
                needsBlock = true
              }
            }
          }
          c : ComputesApplication[_,T] => {
            var needsBlock = false
            if containsApplication(c.function) then {
              needsBlock = true
              blocks += c
            }
            for(arg <- c.arguments) {
              if needsBlock then {
                blocks += arg
              } else if containsApplication(param) then {
                needsBlock = true
              }
            }
          }
          c : ComputesSwitch[_,T] => {
            var needsBlock = false
            if containsApplication(c.argument) then {
              needsBlock = true
              blocks += 
            }
          }
        }
        for(i <- 0 until computes.computesArity) {
          impl(computes.getComputesElement(i))
        }
      }
    }
    // assume top-level Computes is a function literal ... be very confused if it isn't
    // this assumption means that impl will pick it up immediately and add it to blocks for us
    impl(computes)
    blocks.toList
  }

  def findFreeVariables[T](computes : Computes[T]) : List[ComputesVar[_]] = {
    val visitedSet = HashSet[ComputesKey]()
    val isBound = HashSet[ComputesKey]()
    val freeVars = ArrayBuffer[ComputesVar[_]]()
    def impl[T](computes : Computes[T]) : Unit = {
      if visitedSet(computes.key) then {
        ()
      } else {
        visitedSet += computes.key
        computes match {
          case c : ComputesVar[T] =>
            if !isBound(c.key) then {
              freeVars += c
            }
          case c : ComputesBinding[_,T] => {
            isBound += c.name.key
          }
          case c : ComputesFunction[_,_] => {
            c.arguments.foreach(isBound += _)
          }
          case _ => ()
        }
        computes.computesIterator.foreach(impl(_))
      }
    }
    impl(computes)
    freeVars.toList
  }

  def codegenExpr[T](computes : Computes[T], vMap : Map[ComputesKey,Expr[Any]])(implicit reflection : Reflection) : Expr[T] = {
    import reflection._
    computes match {
      case c : Computable[T] => ???
      case c : ComputesVar[T] => vMap(c.key).asInstanceOf[Expr[T]]
      case c : ComputesBinding[_,T] => {
        implicit val e1 = c.value.tType
        '{
          val binding = ${ codegenExpr(c.value, vMap) }
          ${ codegenExpr(c.body, vMap + ((c.name.key, '{ binding }))) }
        }
      }
      case c : ComputesExpr[T] => {
        def proc(inP : List[Computes[_]], outP : List[Expr[_]]) : Expr[T] = inP match {
          case Nil => c.exprFn(outP)
          case hd :: tl => {
            implicit val e1 = computes.tType
            implicit val e2 = hd.tType
            '{
              val exprParam = ${ codegenExpr(hd, vMap).asInstanceOf[Expr[hd.T]] }
              ${ proc(tl, outP ++ List('{ exprParam })) }
            }
          }
        }
        proc(c.params, Nil)
      }
      case c : ComputesApplication[_,T] => ???
      case c : ComputesSwitch[_,T] => {
        val arg = codegenExpr(c.argument, vMap)
        Match(
          arg.unseal,
          (for((v,r) <- c.cases)
            yield CaseDef(
              Pattern.Value(codegenExpr(v, vMap).unseal),
              None,
              impl(r, vMap).unseal))
          ++ c.default.map(d =>
              List({
                // our unsuspecting branch donor, from whom we will steal the default branch
                val bloodSacrifice = '{ ${ arg } match { case _ => ${ codegenExpr(d, vMap) } } }
                bloodSacrifice.unseal match {
                  case IsInlined(inl) => { // strip off an Inlined node that gets in our way
                    inl.body match {
                      case IsMatch(m) => {
                        m.cases.head // if you can't make, it steal it...
                                     // this is a terrible trick that should probably be replaced
                      }
                    }
                  }
                }
              })).getOrElse(Nil)).seal
      }
      case c : ComputesFunction[_,_] => {
        val freeVariables = findFreeVariables(c)
        val refs : List[Expr[Any]] = freeVariables.map(v => vMap(v.key))   
        val closureExpr : Expr[Array[Any]] = if !refs.isEmpty then {
          Apply(Ref(definitions.Array_apply), refs.map(_.unseal)).seal.cast[Array[Any]]
        } else {
          '{ null }
        }
        '{ ( ${ pcMap(c.key).toExpr }, ${ closureExpr } ) }
      }
    }
  }

  def codegenBlock[A,R](computes : ComputesFunction[A,R], pcMap : Map[ComputesKey,Int], arg : Expr[A], closure : Expr[Array[Any]],
                        pushFStack : (Expr[Int],Expr[Array[Any]])=>Expr[Unit],
                        pushDStack : Expr[Any]=>Expr[Unit], popDStack : Expr[Any])
                       (implicit reflection : Reflection): Expr[Unit] = {
    import reflection._
    def impl[T](computes : Computes[T], vMap : Map[ComputesKey,Expr[Any]]) : Expr[Any] =
      if containsApplication(computes) then {
        computes match {
          case c : ComputesBinding[_,T] => {
            implicit val e1 = c.value.tType
            '{
              val binding = ${ codegenExpr(c.value, vMap) }
              ${ impl(c.body, vMap + ((c.name.key, '{ binding }))) }
            }
          }
          case c : ComputesApplication[_,T] => {
            '{
              val (fPc,fClosure) = ${ 
                // TODO assert !containsApplication(c.function), needs to be included in complexify
                codegenExpr(c.function, vMap).asInstanceOf[Expr[(Int,Array[Any])]]
              }
              ${ pushFStack('{ fPc }, '{ fClosure }) }
              ${ 
            }
          }
        }
      } else {
        pushDStack(codegenExpr(computes, vMap))
      }
      
      computes match {
      case c : Computable[T] => ???
      case c : ComputesVar[T] => vMap(c.key).asInstanceOf[Expr[T]]
      case c : ComputesBinding[_,T] => {
        implicit val e1 = c.value.tType
        '{
          val binding = ${ impl(c.value, vMap) }
          ${ impl(c.body, vMap + ((c.name.key, '{ binding }))) }
        }
      }
      case c : ComputesExpr[T] => {
        def proc(inP : List[Computes[_]], outP : List[Expr[_]]) : Expr[T] = inP match {
          case Nil => c.exprFn(outP)
          case hd :: tl => {
            implicit val e1 = computes.tType
            implicit val e2 = hd.tType
            '{
              val exprParam = ${ impl(hd, vMap).asInstanceOf[Expr[hd.T]] }
              ${ proc(tl, outP ++ List('{ exprParam })) }
            }
          }
        }
        proc(c.params, Nil)
      }
      case c : ComputesApply[_,T] => {
        '{
          val fn = ${ impl(c.function, vMap).asInstanceOf[Expr[(Int,Array[Any])]] }
          ${ pushStack('{ fn }) } // TODO, FStack and DStack; simple values are returned, possible callsites manipulate stack
          ${ impl(c.argument, vMap) }
        }
      }
      case c : ComputesSwitch[_,T] => {
        val arg = impl(c.argument, vMap)
        Match(
          arg.unseal,
          (for((v,r) <- c.cases)
            yield CaseDef(
              Pattern.Value(impl(v, vMap).unseal),
              None,
              impl(r, vMap).unseal))
          ++ c.default.map(d =>
              List({
                // our unsuspecting branch donor, from whom we will steal the default branch
                val bloodSacrifice = '{ ${ arg } match { case _ => ${ impl(d, vMap) } } }
                bloodSacrifice.unseal match {
                  case IsInlined(inl) => { // strip off an Inlined node that gets in our way
                    inl.body match {
                      case IsMatch(m) => {
                        m.cases.head // if you can't make, it steal it...
                                     // this is a terrible trick that should probably be replaced
                      }
                    }
                  }
                }
              })).getOrElse(Nil)).seal
      }
      case c : ComputesFunction[_,_] => {
        val freeVariables = findFreeVariables(c)
        val refs : List[Expr[Any]] = freeVariables.map(v => vMap(v.key))   
        val closureExpr : Expr[Array[Any]] = if !refs.isEmpty then {
          Apply(Ref(definitions.Array_apply), refs.map(_.unseal)).seal.cast[Array[Any]]
        } else {
          '{ null }
        }
        '{ ( ${ pcMap(c.key).toExpr }, ${ closureExpr } ) }
      }
    }

    // bind all closed over variables to local names and add them to scope
    var withBindings : Map[ComputesKey,Expr[Any]] => Expr[Any] = impl(computes.body, _)
    for((v,idx) <- findFreeVariables(computes).zipWithIndex) {
      withBindings =
        vMap => '{
          val closureVar = ${ closure }(${ idx.toExpr })
          ${ withBindings(vMap + ((v.key, '{ closureVar }))) }
        }
    }
    withBindings(Map(computes.arg.key -> arg))
  }*/

  def reifyCall[Arg : Type, Result : Type](computes : Computes[Arg=>Result], arg : Expr[Arg])
                                          (implicit reflection: Reflection) = {
    val noLazy = eliminateLazyRefs(computes)
    val inlinedComputes = performInlining(noLazy)
    val flattenedComputes = flatten(inlinedComputes)

    ???
    /*val reboundComputes = inferBindings(flattenedComputes)
    val complexifiedComputes = complexify(reboundComputes)

    val rootKey = complexifiedComputes.key

    val blocks = getBlocks(complexifiedComputes)

    println(blocks)
    val pcMap = blocks.zipWithIndex.map((block, idx) => (block.key, idx)).toMap
    import reflection._
    val expr = '{
      val stack = ArrayStack[(Int,Array[Any])]()
      stack.push((${ pcMap(rootKey).toExpr }, null))
      var reg : Any = ${ arg }
      while(!stack.isEmpty) {
        val (pc, closure) = stack.pop
        reg = ${
          Match(
            '{ pc }.unseal,
            blocks.map(block => {
              implicit val e1 = block.arg.tType
              type AT = block.AT // avoid bug? block.arg.T does not work
              CaseDef(
                Pattern.Value(Literal(Constant.Int(pcMap(block.key)))),
                None,
                codegenBlock(
                  block,
                  pcMap,
                  '{ reg.asInstanceOf[AT] },
                  '{ closure },
                  (fn => '{ stack.push( ${ fn } ) })).unseal)
            })).seal
        }
      }
      reg.asInstanceOf[Result]
    }
    println(expr.show) // DEBUG
    expr*/
  }

  // problem: even if the input expression is globally reachable, we can't tell here because of how
  // parameters work... user has to re-write this one line anywhere they want to use this
  /* implicit class ComputesFnCallCompiler[Arg, Result](inline computes : Computes[Arg=>Result]) {
    inline def reifyCall(arg : Arg) : Result = ${ reifyCallImpl(computes, '{arg}) }
  } */
  
  implicit val ComputesIntOpsOverridesPlus : OverridesPlus[Int,Int,Int] = new {
    def +(lhs : Computes[Int], rhs : Computes[Int]) : Computes[Int] =
      expr((lhs, rhs), t => t match { case (lhs,rhs) => '{ ${ lhs } + ${ rhs } }})
  }
  
  implicit class ComputesIntOps(lhs : Computes[Int]) {
    def -(rhs : Computes[Int]) : Computes[Int] =
      expr((lhs, rhs), t => t match { case (lhs,rhs) => '{ ${ lhs } - ${ rhs } }})
  }

  implicit class ComputesTuple2[T1, T2](tpl : (Computes[T1],Computes[T2])) extends Computable[(T1,T2)]()('[(${ tpl._1.tType },${ tpl._2.tType })]) {
    var tuple = tpl

    override def shallowClone = ComputesTuple2(tuple)

    override def computesArity = 0
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
      // expr(tuple : (Computes[T1],Computes[T2]), (etpl : (Expr[T1],Expr[T2])) => '{ (${ etpl._1 }, ${ etpl._2 }) })
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

  def let[V : Type,T : Type](value : Computes[V], body : Computes[V=>T]) : Computes[T] = body(value)

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

val add1 : Computes[Int=>Int] =
  (i : Computes[Int]) => i+const(1)

val countdown : Computes[Int=>Boolean] =
  (i : Computes[Int]) =>
    i.switch(
      List(const(0) -> const(true)),
      default=countdown(i-const(1)))

val unimap : Computes[((List[Int],Int=>Int))=>List[Int]] =
  (args : Computes[(List[Int],Int=>Int)]) =>
    let(expr(args, args => '{ ${ args }._1 }),
      (list : Computes[List[Int]]) =>
        let(expr(args, args => '{ ${ args }._2 }),
          (fn : Computes[Int=>Int]) =>
            list.isEmpty.switch(
              List(
                const(true) -> expr((), _ => '{ Nil }),
                const(false) ->
                  expr((fn(list.head), unimap((list.tail, fn))),
                    tpl => tpl match { case (mhd,mtl) => '{ ${ mhd } :: ${ mtl } } })))))

val unimapAdd1 : Computes[List[Int]=>List[Int]] =
  (list : Computes[List[Int]]) =>
    unimap(list, add1)

inline def doAdd1(i : Int) : Int = ${ Computes.reifyCall(add1, '{ i }) }

inline def doCountdown(i : Int) : Boolean = ${ Computes.reifyCall(countdown, '{ i }) }

inline def doUnimapAdd1(list : List[Int]) : List[Int] = ${ Computes.reifyCall(unimapAdd1, '{ list }) }

