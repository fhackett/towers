package towers.computes

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}

import quoted._
import tasty._

class ComputesKey()

sealed abstract class Computes[Tp : Type] {
  type T = Tp
  val tType = implicitly[Type[T]]
  val key = ComputesKey()
  val auxKey = ComputesKey() // used in codegen to avoid mixing this with var keys
  val auxVar : ComputesVar[Tp]

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

opaque type ==>[Args, Result] = (Int,Array[Any])

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

class ComputesByKey[T : Type](var link : ComputesKey, var binding : Computes[T] = null) extends Computes[T] {
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
  val auxVar = ComputesVar[T]()
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
  val auxVar = ComputesVar[T]()
  lazy val computes = ref
  // this node should not survive the initial pass to eliminate it, any attempt to use these signifies catastrophic failure
  override def shallowClone = ???
  override def setComputesElement(n : Int, v : Computes[_]) = ???
  override def getComputesElement(n : Int) = computes.getComputesElement(n)
  override def computesArity = computes.computesArity
  override def tryFold = ???
}

class ComputesFunction[FnType : Type, Result : Type](val parameters : List[ComputesVar[_]], var body : Computes[Result]) extends Computes[FnType] {
  val auxVar = ComputesVar[T]()
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
  val auxVar = ComputesVar[T]()
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
    ) extends ComputesFunction[Arg1==>Result,Result](List(arg1), fn(arg1))

  implicit class ComputesFunction2[
    Arg1 : Type, Arg2 : Type,
    Result : Type](
      fn : (Computes[Arg1], Computes[Arg2]) => Computes[Result]
    )(implicit
      arg1 : ComputesVar[Arg1],
      arg2 : ComputesVar[Arg2]
    ) extends ComputesFunction[(Arg1,Arg2)==>Result,Result](List(arg1, arg2), fn(arg1, arg2))

  implicit class ComputesFunction3[
    Arg1 : Type, Arg2 : Type, Arg3 : Type,
    Result : Type](
      fn : (Computes[Arg1], Computes[Arg2], Computes[Arg3]) => Computes[Result]
    )(implicit
      arg1 : ComputesVar[Arg1],
      arg2 : ComputesVar[Arg2],
      arg3 : ComputesVar[Arg3]
    ) extends ComputesFunction[(Arg1,Arg2,Arg3)==>Result,Result](List(arg1, arg2, arg3), fn(arg1, arg2, arg3))

  implicit class ComputesApplication1[Arg1 : Type, Result : Type](fn : =>Computes[Arg1==>Result]) {
    def apply(arg1 : Computes[Arg1]) : Computes[Result] = ComputesApplication(List(arg1), ref(fn))
  }

  implicit class ComputesApplication2[Arg1 : Type, Arg2 : Type, Result : Type](fn : =>Computes[(Arg1,Arg2)==>Result]) {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2]) : Computes[Result] = ComputesApplication(List(arg1, arg2), ref(fn))
  }

  implicit class ComputesApplication3[Arg1 : Type, Arg2 : Type, Arg3 : Type, Result : Type](fn : =>Computes[(Arg1,Arg2,Arg3)==>Result]) {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2], arg3 : Computes[Arg3]) : Computes[Result] =
      ComputesApplication(List(arg1, arg2, arg3), ref(fn))
  }

  trait OverridesPlus[Lhs,Rhs,Out] {
    def +(lhs : Computes[Lhs], rhs : Computes[Rhs]) : Computes[Out]
  }

  def eliminateLazyRefs[T](computes : Computes[T], vSet : Set[ComputesKey] = Set.empty) : Computes[T] = {
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
    val indirects = ArrayBuffer[ComputesByKey[_]]()
    val isRecursive = HashSet[ComputesKey]()

    def impl[T](computes : Computes[T], inKey : Boolean) : Computes[T] = {
      if substitutions.contains(computes.key) then {
        val sub = substitutions(computes.key)
        if sub == null then {
          isRecursive += computes.key
          val rec = ComputesByKey(computes.key)(computes.tType)
          indirects += rec
          rec
        } else {
          sub.asInstanceOf[Computes[T]]
        }
      } else {
        substitutions(computes.key) = null
        computes match {
          case c : ComputesByKey[T] => {
            indirects += c
            if !substitutions.contains(c.link) then {
              c.binding = impl(c.binding, true)
            }
            substitutions(c.key) = c
            c
          }
          case _ => {
            for(i <- 0 until computes.computesArity) {
              computes.setComputesElement(i, impl(computes.getComputesElement(i), false))
            }
            val result = computes.tryFold match {
              case Some(folded) => impl(eliminateLazyRefs(folded, substitutions.keySet.toSet), false)
              case None => computes
            }
            if isRecursive(computes.key) && !inKey then {
              val rec = ComputesByKey(computes.key, result)(computes.tType)
              indirects += rec
              substitutions(computes.key) = rec
              rec
            } else {
              substitutions(computes.key) = result
              result
            }
          }
        }
      }
    }

    val result = impl(computes, false)
    for(indirect <- indirects) {
      while(substitutions.contains(indirect.link) && indirect.link != substitutions(indirect.link).key) {
        val bind = substitutions(indirect.link)
        indirect.link = bind.key
        val b = indirect.binding
        indirect.binding = bind.asInstanceOf[b.type]
      }
    }
    result
  }

  def flatten[T](computes : Computes[T]) : Computes[T] = {
    val substitutions = HashMap[ComputesKey,Computes[_]]()
    val indirects = ArrayBuffer[ComputesByKey[_]]()
    val isRecursive = HashSet[ComputesKey]()

    def impl[T](computes : Computes[T], inKey : Boolean) : Computes[T] = {
      if substitutions.contains(computes.key) then {
        val sub = substitutions(computes.key)
        if sub == null then {
          isRecursive += computes.key
          val rec = ComputesByKey(computes.key)(computes.tType)
          indirects += rec
          rec
        } else {
          sub.asInstanceOf[Computes[T]]
        }
      } else {
        substitutions(computes.key) = null
        computes match {
          case c : ComputesByKey[T] => {
            if substitutions.contains(c.link) then {
              val sub = substitutions(c.link)
              if sub == null then {
                indirects += c
                c.binding = null
              } else {
                c.binding = sub.asInstanceOf[Computes[T]]
                c.link = sub.key
              }
              substitutions(c.key) = c
            } else {
              substitutions(c.key) = c
              val rec = impl(c.binding, true)
              c.binding = rec
              c.link = rec.key
            }
            c
          }
          case _ => {
            for(i <- 0 until computes.computesArity) {
              computes.setComputesElement(i, impl(computes.getComputesElement(i), false))
            }
            val result = computes match {
              case c : Computable[T] => impl(eliminateLazyRefs(c.flatten, substitutions.keySet.toSet), false)
              case _ => computes
            }
            if isRecursive(computes.key) && !inKey then {
              val rec = ComputesByKey(result.key, result)(computes.tType)
              substitutions(computes.key) = rec
              rec
            } else {
              substitutions(computes.key) = result
              result
            }
          }
        }
      }
    }

    val result = impl(computes, false)
    for(indirect <- indirects) {
      val bind = substitutions(indirect.link)
      Predef.assert(indirect.binding == null)
      val b = indirect.binding
      def collapseKeys[T](computes : Computes[T]) : Computes[T] = computes match {
        case c : ComputesByKey[T] => {
          Predef.assert(c.binding != null)
          c.binding
        }
        case _ => computes
      }
      val binding = collapseKeys(bind.asInstanceOf[b.type])
      indirect.binding = binding
      indirect.link = binding.key
    }
    result
  }

  type BasicBlock = (Map[ComputesKey,Int],Map[ComputesKey,Expr[_]],Expr[Any],Expr[Any]=>Expr[Unit], Expr[Int]=>Expr[Unit], Reflection)=>Expr[Unit]
  type Continuation[T] = (Expr[T],Map[ComputesKey,Int],Map[ComputesKey,Expr[_]],Expr[Any],Expr[Any]=>Expr[Unit], Expr[Int]=>Expr[Unit], Reflection)=>Expr[Unit]

  def getBasicBlocks[T](computes : Computes[T]) : List[(ComputesKey,BasicBlock)] = {
    /*val containsApplication = HashSet[ComputesKey]()
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
    }*/
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
                  impl(c.body).filter(v => v != c.name))
              case c : ComputesFunction[_,T] =>
                impl(c.body).filter(v => !c.parameters.contains(v))
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

    val blocks = ArrayBuffer[(ComputesKey,BasicBlock)]()
    ;{
      val visitedSet = HashSet[ComputesKey]()

      def bindVars(names : List[ComputesVar[_]], values : List[Expr[_]], reflection : Reflection, scope : Map[ComputesKey,Expr[_]]=>Expr[Unit]) : Expr[Unit] = {
        def doIt(nv : List[(ComputesVar[_],Expr[_])], vMap : Map[ComputesKey,Expr[_]]) : Expr[Unit] = nv match {
          case Nil => scope(vMap)
          case (name, v) :: tl => {
            implicit val e1 = name.tType
            '{
              val bind = ${ v.asInstanceOf[Expr[name.T]] }
              ${ doIt(tl, vMap + ((name.key, '{ bind }))) }
            }
          }
        }
        doIt(names zip values, Map.empty)
        /*
        import reflection._
        Block(
          for((name, value) <- names zip values)
            yield {
              implicit val e1 = name.tType
              val s = '{ val bind : ${ name.tType } = ${ value.asInstanceOf[Expr[name.T]] } }.unseal
              println(s)
              ???
            },
          scope(null).unseal).seal.cast[Unit]*/
      }

      def pushClosure(values : List[Expr[_]], pushData : Expr[Any]=>Expr[Unit], reflection : Reflection, scope : Expr[Unit]) : Expr[Unit] = {
        import reflection._
        Block(
          values.map(pushData(_).unseal),
          scope.unseal).seal.cast[Unit]
      }

      def bindSequence(seq : List[Computes[_]], closure : List[ComputesVar[_]], singleUse : Boolean, after : BasicBlock) : BasicBlock = {
        val cMap = HashMap[ComputesKey,List[ComputesVar[_]]]()
        seq.foldLeft(Nil : List[ComputesVar[_]])((acc, s) => {
          cMap(s.key) = acc
          s.auxVar :: acc
        })
        val (_, result) = seq.foldRight((null : ComputesKey, after))((s, acc) => {
          val (next, after) = acc
          val fullClosure = cMap(s.key) ++ orderedSetMerge(closure, if next != null then nodeClosures(next) else Nil)
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
        })
        result
      }

      // if cont is null, just skip that part and leave whatever you were going to pass to it on the data stack
      def impl[T](computes : Computes[T], closure : List[ComputesVar[_]], cont : Continuation[T]) : BasicBlock = {
        print("CL "); print(computes); print(" "); print(closure); print(" || "); println(nodeClosures(computes.key))
        val result : BasicBlock = computes match {
          case c : ComputesByKey[T] =>
            c.binding match {
              case c : ComputesFunction[_,T] => impl(c, closure, cont)
              case _ => {
                implicit val e1 = c.tType
                if !visitedSet(c.link) then {
                  visitedSet += c.link
                  val body = impl(c.binding, closure, null)
                  val reverseClosure = nodeClosures(c.link).reverse
                  blocks += ((c.link, (pcMap, vMap, popData, pushData, pushPC, reflection) => {
                    bindVars(reverseClosure, reverseClosure.map(v => '{ ${ popData }.asInstanceOf[${ v.tType }] }), reflection, vMap2 => {
                      print("l clos "); print(vMap ++ vMap2); println(c)
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
                    print("l pre "); print(vMap); println(c)
                    if cont != null then {
                      pushClosure(closure.map(v => vMap(v.key)), pushData, reflection, pushPC(pcMap(c.auxKey).toExpr))
                    } else {
                      '{}
                    }
                  }
                  ${ pushClosure(nodeClosures(c.link).map(v => vMap(v.key)), pushData, reflection, pushPC(pcMap(c.link).toExpr)) }
                }
              }
            }
          case c : ComputesVar[T] => {
            (pcMap, vMap, popData, pushData, pushPC, reflection) => {
              print("v "); print(vMap); println(c.key)
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
                    print("app clos "); print(vMap ++ vMap2); println(c)
                    cont('{ ret }, pcMap, vMap ++ vMap2, popData, pushData, pushPC, reflection)
                  })
                }
              }))
              blocks += block
            }

            val argBlocks = HashMap[ComputesKey,BasicBlock]()
            c.arguments.foldRight(null.asInstanceOf[ComputesKey])((arg, nextKey) => {
              val fullClosure = orderedSetMerge(closure, if nextKey != null then nodeClosures(nextKey) else Nil)
              val b = impl(
                arg,
                fullClosure,
                if nextKey != null then {
                  (argVal, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                    ${
                      print("arg "); print(vMap); println(arg)
                      pushData(argVal)
                    }
                    ${ argBlocks(nextKey)(pcMap, vMap, popData, pushData, pushPC, reflection) }
                  }
                } else null)
              argBlocks(arg.key) = (pcMap, vMap, popData, pushData, pushPC, reflection) => {
                print("arg pre "); print(vMap); println(arg)
                b(pcMap, vMap, popData, pushData, pushPC, reflection)
              }
              arg.key
            })

            val fullClosure = orderedSetMerge(closure, if !c.arguments.isEmpty then nodeClosures(c.arguments.head.key) else Nil)
            impl(c.function, fullClosure, (fn, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
              // if we have a continuation then push block to return to, else we are a leaf call
              ${
                print("app "); print(vMap); println(c)
                if cont != null then {
                  // push locals left to right
                  pushClosure(closure.map(v => vMap(v.key)), pushData, reflection, pushPC(pcMap(c.auxKey).toExpr))
                } else {
                  '{}
                }
              }
              val fnV = ${ fn }.asInstanceOf[(Int,Array[Any])]
              ${ pushPC('{ fnV._1 }) }
              ${ pushData('{ fnV._2 }) }
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
                val reverseParams = c.parameters.reverse
                val fClosure = nodeClosures(c.key)
                bindVars(reverseParams, reverseParams.map(p => '{ ${ popData }.asInstanceOf[${ p.tType }] }), reflection, vMap2 => '{
                  val closureVal = ${ popData }.asInstanceOf[Array[Any]]
                  ${
                    print("fn args "); print(vMap ++ vMap2); println(c)
                    bindVars(
                      fClosure,
                      for((v, i) <- fClosure.zipWithIndex)
                        yield '{ closureVal(${ i.toExpr }).asInstanceOf[${ v.tType }] },
                      reflection,
                      vMap3 => {
                        print("fn clos "); print(vMap3); println(c)
                        body(pcMap, vMap ++ vMap2 ++ vMap3, popData, pushData, pushPC, reflection)
                      })
                  }
                })
              }))
              blocks += block
            }
            (pcMap, vMap, popData, pushData, pushPC, reflection) => {
              import reflection._
              val refs = nodeClosures(c.key).map(v => vMap(v.key))
              val closureExpr : Expr[Array[Any]] = if !refs.isEmpty then
                Apply(Ref(definitions.Array_apply), refs.map(_.unseal)).seal.cast[Array[Any]]
              else
                '{ null }
              '{
                val fn = (${ pcMap(c.body.key).toExpr }, ${ closureExpr })
                ${
                  print("ffn "); print(vMap); println(c)
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
                print("bind "); print(vMap ++ vMap2); println(c)
                body(pcMap, vMap ++ vMap2, popData, pushData, pushPC, reflection)
              }))
          }
          case c : ComputesSwitch[_,T] => {
            implicit val e1 = c.tType

            if cont != null then {
              val block : (ComputesKey, BasicBlock) = ((c.auxKey, (pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                val ret = ${ popData }.asInstanceOf[T]
                ${
                  val reverseClosure = closure.reverse
                  bindVars(reverseClosure, reverseClosure.map(v => '{ ${ popData }.asInstanceOf[${ v.tType }] }), reflection, vMap2 => {
                    print("switch clos "); print(vMap ++ vMap2); println(c)
                    cont('{ ret }, pcMap, vMap ++ vMap2, popData, pushData, pushPC, reflection)
                  })
                }
              }))
              blocks += block
            }

            val outputs = c.cases.map(c => c._2.key -> impl(c._2, closure, null)).toMap
            val default = c.default.map(impl(_, closure, null))

            val bodyClosure = c.cases.map(a => nodeClosures(a._2.key)).foldLeft(c.argument.auxVar :: closure)(orderedSetMerge)
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
                  Match(
                    vMap(c.argument.auxVar.key).unseal,
                    (for((v,r) <- c.cases)
                      yield CaseDef(
                        Pattern.Value(vMap(v.auxVar.key).unseal),
                        None,
                        outputs(r.key)(pcMap, vMap, popData, pushData, pushPC, reflection).unseal))
                    ++ default.map(d =>
                        List({
                          // hack: steal default branch from donor match expression
                          val bloodSacrifice = '{
                            ??? match {
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
          case c : ComputesExpr[T] => {
            implicit val e1 = c.tType

            bindSequence(c.parameters, closure, false,
              (pcMap, vMap, popData, pushData, pushPC, reflection) => '{
                val result = ${ c.exprFn(c.parameters.map(p => vMap(p.auxVar.key))) }
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

      /*// this assumes the root block results in a function, pushing it and its closure onto the stack for execution
      // (which is what has to happen if we are called from reifyCall)
      implicit val e1 = computes.tType
      blocks += ((computes.key, impl(computes, List.empty, (fn, pcMap, vMap, popData, pushData, pushPC, reflection) => '{
        val (pc, clos) = ${ fn }.asInstanceOf[(Int,Array[Any])]
        ${ pushData('{ clos }) }
        ${ pushPC('{ pc }) }
      })))*/
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

    def impl[T](computes : Computes[T])/*(reflection : Reflection)*/ : Unit = {
      for(i <- 0 until indentation) {
        print("  ")
      }
      print(computes.key); print("; ")
      if names.contains(computes.key) then {
        print("<>"); println(names(computes.key))
      } else {
        names(computes.key) = freshName
        print(names(computes.key)); print(": ")
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

  def reifyCall[A1 : Type, R : Type](computes : Computes[A1==>R], a1 : Expr[A1])
                                    (implicit reflection : Reflection) = {
    reify(computes(expr((), _ => a1)))
  }

  def reify[T : Type](computes : Computes[T])(implicit reflection: Reflection) = {
    println("RAW")
    printComputes(computes)
    val noLazy = eliminateLazyRefs(computes)
    println("NOLAZY")
    printComputes(noLazy)
    //val inlinedComputes = performInlining(noLazy)
    //printComputes(inlinedComputes)
    //val flattenedComputes = flatten(inlinedComputes)
    //printComputes(flattenedComputes)
    //val inlinedComputes2 = performInlining(flattenedComputes)
    
    val flattenedComputes = flatten(noLazy)
    println("FLATTENED")
    printComputes(flattenedComputes)

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
      dataStack.pop.asInstanceOf[T]
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

  def let[V : Type,T : Type](value : Computes[V], body : Computes[V==>T]) : Computes[T] = body(value)

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

val add1 : Computes[Int==>Int] =
  (i : Computes[Int]) => i+const(1)

val add2 : Computes[Int==>Int] =
  (i : Computes[Int]) => add1(add1(i))

val countdown : Computes[Int==>Boolean] =
  (i : Computes[Int]) =>
    i.switch(
      List(const(0) -> const(true)),
      default=countdown(i-const(1)))

val add1AddedL : Computes[Int==>Int] =
  (i : Computes[Int]) =>
    i + add1(i)

val add1AddedR : Computes[Int==>Int] =
  (i : Computes[Int]) =>
    add1(i) + i

/*val unimap : Computes[((List[Int],Int=>Int))=>List[Int]] =
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
                    tpl => tpl match { case (mhd,mtl) => '{ ${ mhd } :: ${ mtl } } })))))*/
val unimap : Computes[(List[Int],Int==>Int)==>List[Int]] =
  (list : Computes[List[Int]], fn : Computes[Int==>Int]) =>
    list.isEmpty.switch(
      List(
        const(true) -> expr((), _ => '{ Nil }),
        const(false) ->
          expr((fn(list.head), unimap(list.tail, fn)),
            tpl => tpl match { case (mhd,mtl) => '{ ${ mhd } :: ${ mtl } } })))

val unimapAdd1 : Computes[List[Int]==>List[Int]] =
  (list : Computes[List[Int]]) =>
    unimap(list, add1)

inline def doAdd1(i : Int) : Int = ${ Computes.reifyCall(add1, '{ i }) }

inline def doAdd2(i : Int) : Int = ${ Computes.reifyCall(add2, '{ i }) }

inline def doCountdown(i : Int) : Boolean = ${ Computes.reifyCall(countdown, '{ i }) }

inline def doAdd1AddedL(i : Int) : Int = ${ Computes.reifyCall(add1AddedL, '{ i }) }

inline def doAdd1AddedR(i : Int) : Int = ${ Computes.reifyCall(add1AddedR, '{ i }) }

inline def doUnimapAdd1(list : List[Int]) : List[Int] = ${ Computes.reifyCall(unimapAdd1, '{ list }) }

