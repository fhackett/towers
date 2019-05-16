package towers.computes

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}

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

    type AT = Arg

    def mapBody(fn : Computes[Result] => Computes[Result]) : ComputesFunction[Arg,Result] = {
      val mapped = ComputesFunction[Arg,Result](_ => fn(body))
      mapped.arg = arg
      mapped
    }
  }

  implicit class ComputesApplicationOp[Arg : Type,Result : Type](fn : =>Computes[Arg=>Result]) {
    def apply(arg : Computes[Arg]) : Computes[Result] = ComputesApply(arg, fn)
  }

  def ensureTraversable[T](computes : Computes[T]) : Unit = {
    val visitedSet = HashSet[ComputesKey]()
    def impl[T](computes : Computes[T]) : Unit = computes match {
      case c : Computable[T] => c.parts.foreach(impl(_))
      case c : ComputesVar[T] => ()
      case c : ComputesBinding[_,_] => {
        impl(c.value)
        impl(c.body)
      }
      case c : ComputesExpr[T] => c.params.foreach(impl(_))
      case c : ComputesApply[_,T] => {
        impl(c.argument)
        if !visitedSet(c.function.key) then {
          visitedSet += c.function.key
          impl(c.function)
        }
      }
      case c : ComputesSwitch[_,T] => {
        impl(c.argument)
        for((v, r) <- c.cases) {
          impl(v)
          impl(r)
        }
        c.default.foreach(impl(_))
      }
      case c : ComputesFunction[_,_] => impl(c.body)
    }
  }

  def removeRedundantIndirects[T](computes : Computes[T]) : Computes[T] = {
    val ingressCounts = HashMap[ComputesKey,Int]()
    ;{
      val visitedSet = HashSet[ComputesKey]()
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
      visitedSet += computes.key
      ingressCounts(computes.key) = 1
      countIngresses(computes)
    }
    ;{
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
      visitedSet += computes.key
      val result = removeSingletonIndirects(computes)
      substitutions(computes.key) = result
      ensureTraversable(result)
      result
    }
  }

  def flatten[T](computes : Computes[T]) : Computes[T] = {
    val visitedSet = HashSet[ComputesKey]()
    val substitutions = HashMap[ComputesKey, Computes[_]]()
    def impl[T](computes : Computes[T]) : Computes[T] = {
      implicit val e1 = computes.tType
      computes match {
        case c : Computable[T] => impl(c.flatten)
        case c : ComputesVar[T] => c
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
    }
    visitedSet += computes.key
    val result = impl(computes)
    substitutions(computes.key) = result
    result
  }

  def inferBindings[T](computes : Computes[T]) : Computes[T] = {
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
  }

  def containsCall[T](computes : Computes[T]) : Boolean = computes match {
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

  def replaceVar[T,V](computes : Computes[T], target : ComputesVar[V], value : Computes[V]) : Computes[T] = {
    val visitedSet = HashSet[ComputesKey]()
    val substitutions = HashMap[ComputesKey,Computes[_]]()
    def impl[T](computes : Computes[T]) : Computes[T] = {
      implicit val e1 = computes.tType
      computes match {
        case c : Computable[T] => ???
        case c : ComputesVar[T] =>
          if c.key == target.key then
            value.asInstanceOf[Computes[T]]
          else
            c
        case c : ComputesBinding[_,T] => ComputesBinding(c.name, impl(c.value), impl(c.body))
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
    }
    visitedSet += computes.key
    val result = impl(computes)
    substitutions(computes.key) = result
    result
  }

  def complexify[T](computes : Computes[T]) : Computes[T] = {
    val visitedSet = HashSet[ComputesKey]()
    val substitutions = HashMap[ComputesKey, Computes[_]]()
    def impl[T](computes : Computes[T]) : Computes[T] = {
      implicit val e1 = computes.tType
      computes match {
        case c : Computable[T] => ???
        case c : ComputesVar[T] => c
        case c : ComputesBinding[_,T] => {
          val value = impl(c.value)
          val body = impl(c.body)
          if containsCall(value) then {
            implicit val e2 = value.tType
            ComputesApply(value, ComputesFunction(v => replaceVar(body, c.name, v)))
          } else {
            ComputesBinding(c.name, value, body)
          }
        }
        case c : ComputesExpr[T] => {
          val params = c.params.map(impl(_))
          val outParams = ArrayBuffer[Computes[_]]()
          def proc(params : List[Computes[_]]) : Computes[T] = params match {
            case Nil =>
              ComputesExpr(outParams.toList, c.exprFn)
            case hd :: tl =>
              if containsCall(hd) then {
                implicit val e2 = hd.tType
                ComputesApply(hd, ComputesFunction(v => {
                  outParams += v
                  proc(tl)
                }))
              } else {
                outParams += hd
                proc(tl)
              }
          }
          proc(params)
        }
        case c : ComputesApply[_,T] => {
          val arg = impl(c.argument)
          if visitedSet(c.function.key) then {
            ComputesApply(arg, substitutions(c.function.key).asInstanceOf[Computes[c.argument.T=>T]])
          } else {
            visitedSet += c.function.key
            val sub = impl(c.function)
            substitutions(c.function.key) = sub
            ComputesApply(arg, sub)
          }
        }
        case c : ComputesSwitch[_,T] => { // for the input + each value to compare against (but not the branches themselves!)
                                          // ensure values do not involve calls or inject as many thunks as needed
          type A = c.argument.T
          val arg = impl(c.argument)
          val cases = for((v,r) <- c.cases) yield (impl(v), impl(r))
          val default = c.default.map(impl(_))
          
          def afterArg(arg : Computes[A]) : Computes[T] = {
            val outCases = ArrayBuffer[(Computes[A],Computes[T])]()
            def proc(cases : List[(Computes[A],Computes[T])]) : Computes[T] = cases match {
              case Nil =>
                ComputesSwitch(arg, outCases.toList, default)
              case (hd @ (v,r)) :: tl =>
                if containsCall(v) then {
                  implicit val e2 = v.tType
                  ComputesApply(v, ComputesFunction(vv => {
                    outCases += ((vv, r))
                    proc(tl)
                  }))
                } else {
                  outCases += hd
                  proc(tl)
                }
            }
            proc(cases)
          }
          if containsCall(arg) then {
            implicit val e2 = arg.tType
            ComputesApply(arg, ComputesFunction(v => afterArg(v)))
          } else {
            afterArg(arg)
          }
        }
        case c : ComputesFunction[_,_] => c.mapBody(impl(_))
      }
    }
    val result = impl(computes)
    substitutions(result.key) = result
    result
  }

  def getBlocks[T](computes : Computes[T]) : List[ComputesFunction[_,_]] = {
    val visitedSet = HashSet[ComputesKey]()
    val blocks = ArrayBuffer[ComputesFunction[_,_]]()
    def impl[T](computes : Computes[T]) : Unit = computes match {
      case c : Computable[T] => ???
      case c : ComputesVar[T] => ()
      case c : ComputesBinding[_,T] => {
        impl(c.value)
        impl(c.body)
      }
      case c : ComputesExpr[T] => c.params.foreach(impl(_))
      case c : ComputesApply[_,T] => {
        impl(c.argument)
        if !visitedSet(c.function.key) then {
          visitedSet += c.function.key
          impl(c.function)
        }
      }
      case c : ComputesSwitch[_,T] => {
        impl(c.argument)
        for((v,r) <- c.cases) {
          impl(v)
          impl(r)
        }
        c.default.foreach(impl(_))
      }
      case c : ComputesFunction[_,_] => {
        blocks += c
        impl(c.body)
      }
    }
    visitedSet += computes.key
    // assume top-level Computes is a function literal ... be very confused if it isn't
    // this assumption means that impl will pick it up immediately and find everything else via its body
    impl(computes)
    blocks.toList
  }

  def codegenBlock[A,R](computes : ComputesFunction[A,R], pcMap : Map[ComputesKey,Int], arg : Expr[A], closure : Expr[Array[Any]],
                      pushStack : Expr[(Int,Array[Any])]=>Expr[Unit])
                     (implicit reflection : Reflection): Expr[Any] = {
    import reflection._
    def impl[T](computes : Computes[T], vMap : Map[ComputesKey,Expr[Any]]) : Expr[Any] = computes match {
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
          ${ pushStack('{ fn }) }
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
        '{ ( ${ pcMap(c.key).toExpr }, null ) } // FIXME: actually generate closures
      }
    }
    impl(computes.body, Map(computes.arg.key -> arg))
  }

  def reifyCall[Arg : Type, Result : Type](computes : Computes[Arg=>Result], arg : Expr[Arg])
                                          (implicit reflection: Reflection) = {
    val inlinedComputes = removeRedundantIndirects(computes)
    val flattenedComputes = flatten(inlinedComputes)
    val reboundComputes = inferBindings(flattenedComputes)
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
    expr
  }

  // problem: even if the input expression is globally reachable, we can't tell here because of how
  // parameters work... user has to re-write this one line anywhere they want to use this
  /* implicit class ComputesFnCallCompiler[Arg, Result](inline computes : Computes[Arg=>Result]) {
    inline def reifyCall(arg : Arg) : Result = ${ reifyCallImpl(computes, '{arg}) }
  } */

}

val add1 : Computes[Int=>Int] =
  (i : Computes[Int]) => ComputesExpr(List(i), es => '{ ${ es(0).asInstanceOf[Expr[Int]] } + 1 })

val countdown : Computes[Int=>Boolean] =
  (i : Computes[Int]) =>
    ComputesSwitch(
      i,
      List((ComputesExpr(List(), es => '{ 0 }), ComputesExpr(List(), es => '{ true }))),
      Some(countdown(ComputesExpr(List(i), es => '{ ${ es(0).asInstanceOf[Expr[Int]] } - 1 }))))

inline def doAdd1(i : Int) : Int = ${ Computes.reifyCall(add1, '{ i }) }

inline def doCountdown(i : Int) : Boolean = ${ Computes.reifyCall(countdown, '{ i }) }

