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
  // this node should not survive the initial pass to eliminate it, any attempt to use these signifies catastrophic failure
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

  def addIndirect(key : ComputesKey, parent : Computes[_], indirects : HashMap[ComputesKey,HashSet[Computes[_]]]) : Unit = {
    var buf = indirects.getOrElseUpdate(key, HashSet())
    buf += parent
  }

  def fixIndirects(key : ComputesKey, patch : Computes[_], indirects : HashMap[ComputesKey,HashSet[Computes[_]]]) : Unit = {
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
    val indirects = HashMap[ComputesKey,HashSet[Computes[_]]]()

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

  def regenerateIndirects[T](computes : Computes[T], parent : Computes[_], indirects : HashMap[ComputesKey,HashSet[Computes[_]]]) : Unit = {
    val visitedSet = HashSet[ComputesKey]()
    def impl[T](computes : Computes[T], parent : Computes[_]) : Unit = computes match {
      case c : ComputesByKey[T] => addIndirect(c.link, parent, indirects)
      case _ =>
        for(c <- computes.computesIterator) {
          impl(c, computes)
        }
    }
  }

  def performInlining[T](computes : Computes[T]) : Computes[T] = {
    val substitutions = HashMap[ComputesKey,Computes[_]]()
    val indirects = HashMap[ComputesKey,HashSet[Computes[_]]]()
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
              regenerateIndirects(f2, parent, indirects) // find any redirects orphaned by the rewrite here
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
    val indirects = HashMap[ComputesKey,HashSet[Computes[_]]]()

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
            regenerateIndirects(inlined, parent, indirects) // find any redirects orphaned by the rewrite here
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

  type BasicBlock = (Map[ComputesKey,Int],Map[ComputesKey,Expr[_]],Expr[_],Expr[_]=>Expr[Unit], Expr[Int]=>Expr[Unit], Reflection)=>Expr[Unit]

  def getBasicBlocks[T](computes : Computes[T]) : List[(ComputesKey,BasicBlock)] = {
    val containsApplication = HashSet[ComputesKey]()
    ;{
      val visitedSet = HashSet[ComputesKey]()
      val visitingSet = HashSet[ComputesKey]()
      val toReexamine = HashMap[ComputesKey,ArrayBuffer[List[Computes[_]]]]()
      def impl[T](computes : Computes[T], path : List[Computes[_]]) : Unit = {
        if visitedSet(computes.key) then {
          () // do nothing, result is already cached in containsApplication
        } else if visitingSet(computes.key) then {
          // this node is inside itself, so we should do the special fix-up thing
          // at the end (see below)
          val reex = toReexamine.getOrElseUpdate(computes.key, ArrayBuffer())
          reex += path
        } else {
          visitingSet += computes.key

          computes match {
            // for our purposes, function applications contain function applications
            case c : ComputesApplication[_,T] => {
              containsApplication += c.key
              computes.computesIterator.foreach(impl(_, List.empty))
            }
            // function literals do not contain applications (even if their bodies do)
            case c : ComputesFunction[_,_] => {
              computes.computesIterator.foreach(impl(_, List.empty))
            }
            case _ => {
              computes.computesIterator.foreach(impl(_, computes :: path))
              if computes.computesIterator.exists((c : Computes[_]) => containsApplication(c.key)) then {
                containsApplication += computes.key
              }
            }
          }

          visitedSet += computes.key
          visitingSet -= computes.key
          // if a recursive reference contains an application, taint all the things that contain it
          // (that's why we keep a path of enclosing Computes)
          if toReexamine.contains(computes.key) then {
            val paths = toReexamine(computes.key)
            toReexamine -= computes.key
            if containsApplication(computes.key) then {
              for(path <- paths; elem <- path) {
                containsApplication += elem.key
              }
            }
          }
        }
      }
      impl(computes, List.empty)
    }
    val nodeClosures = HashMap[ComputesKey,List[ComputesKey]]()
    ;{
      def orderedSetMerge(lhs : List[ComputesKey], rhs : List[ComputesKey]) : List[ComputesKey] = {
        val lset = lhs.toSet
        lhs ++ rhs.filter(!lset(_))
      }

      val toReexamine = HashMap[ComputesKey,ArrayBuffer[List[ComputesKey]]]()
      def impl[T](computes : Computes[T], boundVars : Set[ComputesKey], path : List[ComputesKey]) : List[ComputesKey] = {
        if nodeClosures.contains(computes.key) then {
          val cls = nodeClosures(computes.key)
          if cls == null then {
            val reex = toReexamine.getOrElseUpdate(computes.key, ArrayBuffer())
            reex += path.dropWhile(_ != computes.key).tail
            List.empty
          } else {
            cls
          }
        } else {
          nodeClosures(computes.key) = null

          val result = (computes match {
            case c : ComputesVar[T] => List(c.key)
            case c : ComputesBinding[_,T] =>
              orderedSetMerge(
                impl(c.value, boundVars, computes.key :: path),
                impl(c.body, boundVars + c.key, computes.key :: path))
            case c : ComputesFunction[_,_] =>
              impl(c.body, boundVars ++ c.parameters.map(_.key), computes.key :: path)
            case _ =>
              computes.computesIterator
                .map(impl(_, boundVars, computes.key :: path))
                .foldLeft(List.empty)(orderedSetMerge)
          }).filter(!boundVars(_))

          nodeClosures(computes.key) = result

          if toReexamine.contains(computes.key) then {
            val reex = toReexamine(computes.key)
            toReexamine -= computes.key
            for(path <- reex; elem <- path) {
              nodeClosures(elem) = orderedSetMerge(nodeClosures(elem), result)
            }
          }
          result
        }
      }
      impl(computes, Set.empty, List.empty)
    }

    /*val isReferencedMultiply = HashSet[ComputesKey]()
    ;{
      val visitedSet = HashSet[ComputesKey]()
      def impl[T](computes : Computes[T]) = {
        if visitedSet(computes.key) then {
          isReferencedMultiply += computes.key
        } else {
          visitedSet += computes.key
          computes.computesIterator.foreach(impl(_))
        }
      }
      impl(computes)
    }*/

    type Continuation = (Expr[_],Map[ComputesKey,Int],Map[ComputesKey,Expr[_]],Expr[_],Expr[_]=>Expr[Unit], Expr[Int]=>Expr[Unit], Reflection)=>Expr[Unit]
    val blocks = ArrayBuffer[(ComputesKey,BasicBlock)]()
    ;{
      val visitedSet = HashSet[ComputesKey]()

      // if cont is null, just skip that part and leave whatever you were going to pass to it on the data stack
      def impl[T](computes : Computes[T], closure : List[ComputesKey], cont : Continuation) : BasicBlock = {
        val result : BasicBlock = computes match {
          case c : ComputesVar[T] => {
            (pcMap, vMap, popData, pushData, pushPC, reflection) =>
              if cont == null then pushData(vMap(c.key)) else cont(vMap(c.key), pcMap, vMap, popData, pushData, pushPC, reflection)
          }
          case c : ComputesApplication[_,T] => {
            val ret = ComputesKey()
            if cont != null then {
              blocks += ((ret, (pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                val retVal = ${ popData }
                ${
                  def bindClosuredNames(closure : List[ComputesKey], vMap : Map[ComputesKey,Expr[_]]) : Expr[Unit] = closure match {
                    case Nil => cont('{ retVal }, pcMap, vMap, popData, pushData, pushPC, reflection)
                    case hd :: tl => '{
                      val boundClosure = ${ popData }
                      ${ bindClosuredNames(tl, vMap + ((hd, '{ boundClosure }))) }
                    }
                  }
                  // bind locals backwards (left to right) to account for stack order
                  bindClosuredNames(closure.reverse, vMap)
                }
              }))
            }

            val argBlocks = HashMap[ComputesKey,BasicBlock]()
            c.arguments.foldRight(null.asInstanceOf[ComputesKey])((arg, nextKey) => {
              argBlocks(arg.key) = impl(arg, List.empty, (argVal, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                ${ pushData(argVal) }
                ${ if nextKey != null then argBlocks(nextKey)(pcMap, vMap, popData, pushData, pushPC, reflection) else '{} }
              })
              arg.key
            })

            impl(c.function, closure, (fn, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
              // if we have a continuation then push block to return to, else we are a leaf call
              ${ if cont != null then pushPC(pcMap(ret).toExpr) else '{} }
              // push locals left to right
              ${
                closure.foldLeft('{})((acc, v) => '{
                  ${ acc }
                  ${ pushData(vMap(v)) }
                })
              }
              val (pc, clos) = ${ fn }.asInstanceOf[(Int,Array[Any])]
              ${ pushPC('{ pc }) }
              ${ pushData('{ clos }) }
              ${
                if !c.arguments.isEmpty then
                  argBlocks(c.arguments.head.key)(pcMap, vMap, popData, pushData, pushPC, reflection)
                else
                  '{}
              }
            })
          }
          case c : ComputesFunction[_,_] => {
            // lazily generate function body (incl. stack pop and closure extraction)
            if !visitedSet(c.key) then {
              visitedSet += c.key
              val body = impl(c.body, List.empty, null)
              val block : (ComputesKey,BasicBlock) = ((c.body.key, (pcMap, vMap, popData, pushData, pushPC, reflection) => {
                def bindClosure(idx : Int, closure : List[ComputesKey], closureVal : Expr[Array[Any]], vMap : Map[ComputesKey,Expr[_]]) : Expr[Unit] = closure match {
                  case Nil => body(pcMap, vMap, popData, pushData, pushPC, reflection)
                  case hd :: tl => '{
                    val boundClosure = ${ closureVal }(${ idx.toExpr })
                    ${ bindClosure(idx+1, tl, closureVal, vMap + ((hd, '{ boundClosure }))) }
                  }
                }
                def bindArguments(args : List[ComputesKey], vMap : Map[ComputesKey,Expr[_]]) : Expr[Unit] = args match {
                  case Nil => '{
                    val closure = ${ popData }.asInstanceOf[Array[Any]]
                    ${ bindClosure(0, nodeClosures(c.key), '{ closure }, vMap) }
                  }
                  case hd :: tl => '{
                    val boundArgument = ${ popData }
                    ${ bindArguments(tl, vMap + ((hd, '{ boundArgument }))) }
                  }
                }
                bindArguments(c.parameters.map(_.key).reverse, Map.empty)
              }))
              blocks += block
            }
            (pcMap, vMap, popData, pushData, pushPC, reflection) => {
              import reflection._
              val refs = nodeClosures(c.key).map(vMap(_))
              val closureExpr : Expr[Array[Any]] = if !refs.isEmpty then
                Apply(Ref(definitions.Array_apply), refs.map(_.unseal)).seal.cast[Array[Any]]
              else
                '{ null }
              '{
                val fn = (${ pcMap(c.body.key).toExpr }, ${ closureExpr })
                ${
                  if cont != null then
                    cont('{ fn }, pcMap, vMap, popData, pushData, pushPC, reflection)
                  else
                    pushData('{ fn })
                }
              }
            }
          }
          case c : ComputesBinding[_,T] => {
            val body = impl(c.body, closure, cont)
            impl(c.value, closure, (value, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
              val binding = ${ value }
              ${ body(pcMap, vMap + ((c.name.key, '{ binding })), popData, pushData, pushPC, reflection) }
            })
          }
          case c : ComputesSwitch[_,T] => {
            implicit val e1 = c.tType

            val thunk : Continuation = null /*if c.cases.exists(c => containsApplication(c._2.key)) then
              null
            else
              (v, pcMap, vMap, popData, pushData, pushPC, reflection) => {
                println(vMap)
                vMap(c.key).asInstanceOf[Expr[T=>Unit]](v.asInstanceOf[Expr[T]])
              }*/

            val closureAcc = ArrayBuffer[ComputesKey]()
            val inputs = HashMap[ComputesKey,BasicBlock]()
            val follows = HashMap[ComputesKey,ComputesKey]()
            var prev : ComputesKey = null
            val body = ComputesKey()
            for((in,_) <- c.cases) {
              follows(prev) = in.key
              prev = in.key
              // trick: we know the bound vars here will be used in exactly one place. directly add the expression to the var bindings
              // (this also gets us literals inlined for free! ... unless there is a call after, in which case closuring breaks that)
              inputs(in.key) = impl(in, closure ++ closureAcc.toList, (value, pcMap, vMap, popData, pushData, pushPC, reflection) =>
                inputs(follows(in.key))(pcMap, vMap + ((in.key, value)), popData, pushData, pushPC, reflection))
              closureAcc += in.key
            }
            follows(prev) = body

            val outputs = HashMap[ComputesKey,BasicBlock]()
            for((_,out) <- c.cases) {
              outputs(out.key) = impl(out, closure, thunk)
            }

            val default : Option[BasicBlock] = c.default.map(impl(_, closure, thunk))

            val ret = ComputesKey()
            if thunk == null && cont != null then {
              blocks += ((ret, (pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                val retVal = ${ popData }
                ${
                  def bindClosuredNames(closure : List[ComputesKey], vMap : Map[ComputesKey,Expr[_]]) : Expr[Unit] = closure match {
                    case Nil => cont('{ retVal }, pcMap, vMap, popData, pushData, pushPC, reflection)
                    case hd :: tl => '{
                      val boundClosure = ${ popData }
                      ${ bindClosuredNames(tl, vMap + ((hd, '{ boundClosure }))) }
                    }
                  }
                  // bind locals backwards (left to right) to account for stack order
                  bindClosuredNames(closure.reverse, vMap)
                }
              }))
            }

            inputs(body) = impl(c.argument, closure, (arg, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
              var switchResult : T = null.asInstanceOf[T]
              ${
                if thunk == null && cont != null then '{
                  ${ pushPC(pcMap(ret).toExpr) }
                  ${
                    closure.foldLeft('{})((acc, v) => '{
                      ${ acc }
                      ${ pushData(vMap(v)) }
                    })
                  }
                } else {
                  '{}
                }
              }
              ${
                val valueSink : Expr[T=>Unit] = '{ v => switchResult = v }
                import reflection._
                Match(
                  arg.unseal,
                  (for((v,r) <- c.cases)
                    yield CaseDef(
                      Pattern.Value(vMap(v.key).unseal),
                      None,
                      outputs(r.key)(pcMap, vMap + ((c.key, valueSink)), popData, pushData, pushPC, reflection).unseal))
                  ++ default.map(d =>
                      List({
                        // hack: steal default branch from donor match expression
                        val bloodSacrifice = '{
                          ??? match {
                            case _ => ${ d(pcMap, vMap + ((c.key, valueSink)), popData, pushData, pushPC, reflection) }
                          }
                        }
                        bloodSacrifice.unseal match {
                          case IsInlined(inl) => inl.body match {
                            case IsMatch(m) => m.cases.head
                          }
                        }
                      })).getOrElse(Nil)).seal
              }
              ${
                if thunk != null then {
                  if cont != null then {
                    cont('{ switchResult }, pcMap, vMap, popData, pushData, pushPC, reflection)
                  } else {
                    pushData('{ switchResult })
                  }
                } else {
                  '{}
                }
              }
            })
            inputs(follows(null))
          }
          case c : ComputesExpr[T] => {
            implicit val e1 = c.tType

            val closureAcc = ArrayBuffer[ComputesKey]()
            val inputs = HashMap[ComputesKey,BasicBlock]()
            val follows = HashMap[ComputesKey,ComputesKey]()
            var prev : ComputesKey = null
            val body = ComputesKey()
            for(param <- c.parameters) {
              follows(prev) = param.key
              prev = param.key
              inputs(param.key) = impl(param, closure ++ closureAcc.toList, (value, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                val binding = ${ value }
                ${ inputs(follows(param.key))(pcMap, vMap + ((param.key, '{ binding })), popData, pushData, pushPC, reflection) }
              })
              closureAcc += param.key
            }
            follows(prev) = body
            inputs(body) = (pcMap, vMap, popData, pushData, pushPC, reflection) => '{
              val exprResult = ${ c.exprFn(closureAcc.map(vMap(_)).toList) }
              ${
                if cont != null then
                  cont('{ exprResult }, pcMap, vMap, popData, pushData, pushPC, reflection)
                else
                  pushData('{ exprResult })
              }
            }
            inputs(follows(null))
          }
          case n => {
            println(n)
            ??? // Computable, ComputesByKey, ComputesLazyRef (all obsolete at this stage of compilation)
          }
        }
        result
      }

      // this assumes the root block results in a function, pushing it and its closure onto the stack for execution
      // (which is what has to happen if we are called from reifyCall)
      blocks += ((computes.key, impl(computes, List.empty, (fn, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
        val (pc, clos) = ${ fn }.asInstanceOf[(Int,Array[Any])]
        ${ pushData('{ clos }) }
        ${ pushPC('{ pc }) }
      })))
    }
    blocks.toList
  }

  def checkNoComputesByKey[T](computes : Computes[T]) : Unit = {
    val visitedSet = HashSet[ComputesKey]()
    def impl[T](computes : Computes[T]) : Unit = if !visitedSet(computes.key) then {
      visitedSet += computes.key
      computes match {
        case c : ComputesByKey[T] => ???
        case _ => computes.computesIterator.foreach(impl(_))
      }
    }
    impl(computes)
  }

  def reifyCall[Arg : Type, Result : Type](computes : Computes[Arg=>Result], arg : Expr[Arg])
                                          (implicit reflection: Reflection) = {
    val noLazy = eliminateLazyRefs(computes)
    checkNoComputesByKey(noLazy)
    val inlinedComputes = performInlining(noLazy)
    checkNoComputesByKey(inlinedComputes)
    val flattenedComputes = flatten(inlinedComputes)
    checkNoComputesByKey(flattenedComputes)
    //val reboundComputes = inferBindings(flattenedComputes)

    val rootKey = flattenedComputes.key
    val basicBlocks = getBasicBlocks(flattenedComputes)

    //println(blocks)
    val pcMap = basicBlocks.zipWithIndex.map((block, idx) => (block._1, idx)).toMap
    import reflection._
    val expr = '{
      val pcStack = ArrayStack[Int]()
      val dataStack = ArrayStack[Any]()

      // TODO: push more arguments
      pcStack.push(${ pcMap(rootKey).toExpr })

      while(!pcStack.isEmpty) {
        ${
          Match(
            '{ pcStack.pop }.unseal,
            basicBlocks.map({
              case (key,block) =>
                CaseDef(
                  Pattern.Value(Literal(Constant.Int(pcMap(key)))),
                  None,
                  block(
                    pcMap,
                    Map.empty,
                    '{ dataStack.pop },
                    v => '{ dataStack.push(${ v }) },
                    pc => '{ pcStack.push(${ pc }) },
                    reflection).unseal)
            })).seal
        }
      }
      dataStack.pop.asInstanceOf[Result]
    }
    println(expr.show) // DEBUG
    expr
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

