package towers.computes

import Predef.{any2stringadd => _, _} // allow implicits to override +

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}
import scala.collection.{Set,Map}

import quoted._
import tasty._

type ComputesKey = Int
val NoKey = -1

trait KeyContext {
  def getKeyOf(obj : AnyRef) : ComputesKey
}

trait OpContext {
  def substitute[T](subs : Map[ComputesKey,_ <: Computes[_]], computes : Computes[T])(implicit keyCtx : KeyContext) : Option[Computes[T]]
}

sealed abstract class Computes[T : Type] {
  val tType = implicitly[Type[T]]

  private val k1 = new AnyRef
  private val k2 = new AnyRef
  def key(implicit keyCtx : KeyContext) = keyCtx.getKeyOf(k1)
  def auxKey(implicit keyCtx : KeyContext) = keyCtx.getKeyOf(k2)
  val auxVar : ComputesVar[T]

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit opCtx : OpContext, keyCtx : KeyContext) : Computes[T]
  def toComputesSeq : Seq[Computes[_]]

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) : Option[Computes[T]]
}

abstract class Computable[T : Type] extends Computes[T] {
  // translate this Computable into some lower-level implementation
  def flatten : Computes[T]

  val auxVar = ComputesVar[T]()

  //val foldUnderstands : List[ClassTag[Computes[T]]]
  //val flattenProduces : ClassTag[Computes[T]]
}

final class ComputesVar[T : Type]() extends Computes[T] {
  val auxVar = this
  
  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit opCtx : OpContext, keyCtx : KeyContext) = ???
  def toComputesSeq = Seq.empty
  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
}

final class ComputesIndirect[T : Type](var binding : Computes[T]) extends Computes[T] {
  val auxVar = ComputesVar[T]()

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit opCtx : OpContext, keyCtx : KeyContext) = seq match {
    case Seq(binding : Computes[T]) => {
      val clone = ComputesIndirect[T](null)
      clone.binding = opCtx.substitute(Map(this.key -> clone), binding) match {
        case Some(nBinding) => nBinding
        case None => binding
      }
      clone
    }
    case Seq() => ??? // if someone is manipulating something like this, they shouldn't be (don't clone a back reference inside a cycle)
      //ComputesIndirect(null)
  }
  def toComputesSeq =
    if binding != null then {
      Seq(binding)
    } else {
      Seq.empty
    }

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
}

final class ComputesBinding[V, T : Type](val name : ComputesVar[V], val value : Computes[V], val body : Computes[T]) extends Computes[T] {
  val auxVar = ComputesVar[T]()

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit opCtx : OpContext, keyCtx : KeyContext) = seq match {
    case Seq(value : Computes[V], body : Computes[T]) => {
      val newName = ComputesVar[V]()(name.tType)
      ComputesBinding(
        newName,
        value,
        opCtx.substitute(Map(name.key -> newName), body) match {
          case Some(b) => b
          case None => body
        })
    }
  }
  def toComputesSeq = Seq(value, body)

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
}

final class ComputesExpr[T : Type](val parameters : Seq[Computes[_]], val exprFn : Seq[Expr[_]] => Expr[T]) extends Computes[T] {
  val auxVar = ComputesVar[T]()

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit opCtx : OpContext, keyCtx : KeyContext) = ComputesExpr(seq, exprFn)
  def toComputesSeq = parameters
  
  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
}

final class ComputesApplication[FnType, Result : Type](val arguments : Seq[Computes[_]], val function : Computes[FnType]) extends Computes[Result] {
  val auxVar = ComputesVar[Result]()

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit opCtx : OpContext, keyCtx : KeyContext) = seq match {
    case Seq(function : Computes[FnType], arguments :_*) => ComputesApplication(arguments.asInstanceOf[Seq[Computes[_]]], function)
  }
  def toComputesSeq = function +: arguments

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = function match {
    case fn : ComputesFunction[_,Result] =>
      opCtx.substitute((fn.parameters.map(_.key) zip arguments).toMap, fn.body)
    case _ => None
  }
}

class ComputesLazyRef[T : Type](ref : =>Computes[T]) extends Computes[T] {
  val auxVar = ComputesVar[T]()
  lazy val computes = ref

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit opCtx : OpContext, keyCtx : KeyContext) = seq match {
    case Seq(computes : Computes[T]) => ComputesLazyRef(computes)
  }
  def toComputesSeq = Seq(computes)

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
}

class ComputesFunction[FnType <: Computes.==>[_,Result] : Type, Result : Type](val inst : Computes.FnInst[FnType], val parameters : Seq[ComputesVar[_]], val body : Computes[Result]) extends Computes[FnType] {
  val auxVar = ComputesVar[FnType]()

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit opCtx : OpContext, keyCtx : KeyContext) = seq match {
    case Seq(body : Computes[Result]) => {
      val newParams = parameters.map({
        case p : ComputesVar[v] =>
          ComputesVar[v]()(p.tType)
      })
      ComputesFunction[FnType,Result](
        inst,
        newParams,
        opCtx.substitute((parameters.map(_.key) zip newParams).toMap, body).getOrElse(body))
    }
  }
  def toComputesSeq = Seq(body)

  def tryFold(implicit opCts : OpContext, keyCtx : KeyContext) = None
}

final class ComputesSwitch[Arg, Result : Type](
  val argument : Computes[Arg],
  val cases : Seq[(Computes[Arg],Computes[Result])],
  val default : Option[Computes[Result]]
) extends Computes[Result] {
  val auxVar = ComputesVar[Result]()

  private def pairCases(cases : Seq[Computes[_]]) : Seq[(Computes[Arg],Computes[Result])] = {
    @scala.annotation.tailrec
    def impl(cases : Seq[Computes[_]], prefix : ArrayBuffer[(Computes[Arg],Computes[Result])]) : Seq[(Computes[Arg],Computes[Result])] =
      cases match {
        case Seq(arg : Computes[Arg], result : Computes[Result], rest :_*) =>
          impl(rest, prefix += ((arg,result)))
        case Seq() =>
          prefix
      }
    impl(cases, ArrayBuffer())
  }

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit opCtx : OpContext, keyCtx : KeyContext) =
    if seq.length % 2 == 0 then {
      seq match {
        case Seq(argument : Computes[Arg], default : Computes[Result], casesUnpaired :_*) =>
          ComputesSwitch(argument, pairCases(casesUnpaired.asInstanceOf[Seq[Computes[_]]]), Some(default))
      }
    } else {
      seq match {
        case Seq(argument : Computes[Arg], casesUnpaired :_*) =>
          ComputesSwitch(argument, pairCases(casesUnpaired.asInstanceOf[Seq[Computes[_]]]), None)
      }
    }
  def toComputesSeq = (argument +: default.map(Seq(_)).getOrElse(Seq.empty)) ++ cases.flatMap({
    case (arg, result) => Seq(arg, result)
  })

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
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

  trait AnalysisAction[Result] {
    def analyse[T](computes : Computes[T], results : Map[ComputesKey,Result])(implicit keyCtx : KeyContext) : Result
    def merge(left : Result, right : Result)(implicit keyCtx : KeyContext) : Result
    def zeroResult : Result
  }

  def analyse[T,Result](computes : Computes[T], action : AnalysisAction[Result])(implicit keyCtx : KeyContext) : Result = {
    val results = HashMap[ComputesKey,Result]()
    
    def iter[T](computes : Computes[T]) : Result = {
      val visitedSet = HashSet[ComputesKey]()
      def impl[T](computes : Computes[T]) : Result = {
        if visitedSet(computes.key) then {
          results.getOrElse(computes.key, action.zeroResult)
        } else {
          visitedSet += computes.key
          computes.toComputesSeq.foreach(impl(_))
          val result = action.analyse(computes, results)
          val merged = action.merge(results.getOrElse(computes.key, action.zeroResult), result)
          results(computes.key) = merged
          merged
        }
      }
      impl(computes)
    }
    
    // it takes 2 runs to reach fixpoint. 1 to propagate within each cycle, and the second to propagate across any loops
    iter(computes)
    iter(computes)
  }

  implicit object TheOpContext extends OpContext {
    def substitute[T](subs : Map[ComputesKey, _ <: Computes[_]], computes : Computes[T])(implicit keyCtx : KeyContext) : Option[Computes[T]] = {
      //println(s"B SUB $subs")
      //printComputes(computes)
      rewriteOpt(computes, new {
        def apply[T](computes : Computes[T])(implicit opCts : OpContext) : Option[Computes[T]] = {
          if subs.contains(computes.key) then {
            Some(subs(computes.key).asInstanceOf[Computes[T]])
          } else {
            None
          }
        }
      })
    }
  }

  trait RewriteAction {
    def apply[T](computes : Computes[T])(implicit opCtx : OpContext) : Option[Computes[T]]
  }

  def rewriteOpt[T](computes : Computes[T], action : RewriteAction)(implicit keyCtx : KeyContext) : Option[Computes[T]] = {
    val substitutions = HashMap[ComputesKey,Computes[_]]()
    val deadEnds = HashSet[ComputesKey]()
    val isRecursive = HashSet[Computes[_]]()

    def impl[T](computes : Computes[T]) : Option[Computes[T]] = {
      if deadEnds(computes.key) then {
        None
      } else if substitutions.contains(computes.key) then {
        substitutions(computes.key).asInstanceOf[Computes[T]] match {
          case c : ComputesIndirect[T] => {
            if c.binding == null then {
              isRecursive += c // avoid using keys here to avoid wasting a ComputesKey per impl(_) invocation
            }
            Some(c)
          }
          case c => Some(c)
        }
      } else {
        computes match {
          case c : ComputesLazyRef[T] => {
            impl(c.computes) match { // unconditionally erase lazy refs, they add nothing
              case result @ Some(_) => result
              case None => Some(c.computes)
            }
          }
          case c : ComputesIndirect[T] => {
            if c.binding != null then { // if binding is null we are in a recursive call that will eventually set binding
              substitutions(computes.key) = c
              // if processing inside a cycle, set the binding to null to ensure there is no way to follow the cycle from inside the cycle
              val oldBinding = c.binding
              c.binding = null
              c.binding = impl(oldBinding) match {
                case Some(b) => b
                case None => oldBinding
              }
              Some(c)
            } else {
              None
            }
          }
          case _ => {
            val indirect = ComputesIndirect[T](null)(computes.tType)
            substitutions(computes.key) = indirect

            // to explain all the Option, either a recursion changed something or the action changed something
            // in either case we should forward the change, but not if absolutely nothing changed
            
            val seq = computes.toComputesSeq
            val mapped = seq.map(impl(_))
            val beforeAction = if mapped.exists(!_.isEmpty) then {
              Some(computes.likeFromSeq((seq zip mapped).map({
                case (_, Some(c)) => c
                case (c, None) => c
              })))
            } else {
              None
            }

            val actionResult = action(
              beforeAction match {
                case Some(a) => a
                case None => computes
              })
            
            val result = actionResult match {
              case Some(r) => // if the action changed something, recursively try to perform the action until fixpoint
                impl(r) match {
                  case iResult @ Some(_) => iResult
                  case None => actionResult
                }
              case None => beforeAction
            }

            if isRecursive(indirect) then {
              indirect.binding = result.get // for something to reach the indirect something must have changed, so this option will always
                                            // have a value
              // subtle point: we need to alias the original to the binding or we will spuriously reprocess the original
              // we alias the indirect to itself because we have finished processing it
              substitutions(computes.key) = indirect.binding
              substitutions(indirect.key) = indirect
              Some(indirect)
            } else {
              result match {
                case Some(r) => {
                  substitutions(computes.key) = r
                  result
                }
                case None => {
                  deadEnds += computes.key
                  None
                }
              }
            }
          }
        }
      }
    }

    impl(computes)
  }

  def rewrite[T](computes : Computes[T], action : RewriteAction)(implicit keyCtx : KeyContext) : Computes[T] = 
    rewriteOpt(computes, action) match {
      case Some(r) => r
      case None => computes
    }

  def performInlining[T](computes : Computes[T])(implicit keyCtx : KeyContext) : Computes[T] =
    rewrite(computes, new {
      def apply[T](computes : Computes[T])(implicit opCtx : OpContext) : Option[Computes[T]] =
        computes.tryFold
    })

  def flatten[T](computes : Computes[T])(implicit keyCtx : KeyContext) : Computes[T] =
    rewrite(computes, new {
      def apply[T](computes : Computes[T])(implicit opCtx : OpContext) : Option[Computes[T]] =
        computes match {
          case c : Computable[T] => Some(c.flatten)
          case c => None
        }
    })

  type BasicBlock = (Map[ComputesKey,Int],Map[ComputesKey,Expr[_]],Expr[Any],Expr[Any]=>Expr[Unit], Expr[Int]=>Expr[Unit], Reflection)=>Expr[Unit]
  type Continuation[T] = (Expr[T],Map[ComputesKey,Int],Map[ComputesKey,Expr[_]],Expr[Any],Expr[Any]=>Expr[Unit], Expr[Int]=>Expr[Unit], Reflection)=>Expr[Unit]

  def getBasicBlocks[T](computes : Computes[T])(implicit keyCtx : KeyContext) : List[(ComputesKey,BasicBlock)] = {

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
              case c : ComputesIndirect[T] => impl(c.binding)
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
                c.toComputesSeq.foldLeft(Nil : List[ComputesVar[_]])((acc, part) =>
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
          case c : ComputesIndirect[T] =>
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
                bindVars(reverseParams.toList, reverseParams.map(p => '{ ${ popData }.asInstanceOf[${ p.tType }] }).toList, reflection, vMap2 => '{
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
              println(s"CLOS ${c.key} ${nodeClosures(c.key).map(_.key)} VV ${vMap}")
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
              bindSequence(c.argument :: c.cases.map(_._1).toList, bodyClosure, true,
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
                        }).toList
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

            bindSequence(c.parameters.toList, closure, false,
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

  def printComputes[T](computes : Computes[T])(implicit keyCtx : KeyContext) : Unit = {
    
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
      if computes != null then {
        print(s"${computes.key}; ${computes.auxKey}; ${computes.auxVar.key}; ")
        if names.contains(computes.key) then {
          print("<>"); println(names(computes.key))
        } else {
          names(computes.key) = freshName
          print(names(computes.key)); print(": ")
          computes match {
            case c : ComputesFunction[_,_] => {
              println(c.parameters.map(_.key))
            }
            case c : ComputesLazyRef[T] => {
              print(c); print(" :: "); println(c.computes)
            }
            case c : ComputesIndirect[T] => {
              print(c); println(" >>")
              indentation += 1
              impl(c.binding)
              indentation -= 1
            }
            case c => println(c)
          }
          indentation += 1
          for(c <- computes.toComputesSeq) {
            impl(c)
          }
          indentation -= 1
        }
      } else {
        println("NULL")
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
    val keyMap = HashMap[AnyRef,ComputesKey]()
    implicit val keyCtx : KeyContext = new KeyContext {
      def getKeyOf(obj : AnyRef) = {
        if keyMap.contains(obj) then {
          keyMap(obj)
        } else {
          val key = keyCounter
          keyMap(obj) = key
          keyCounter += 1
          key
        }
      }
    }
    println("RAW")
    printComputes(computes)
    val inlinedComputes = performInlining(computes)
    println("INLINE1")
    printComputes(inlinedComputes)
    val flattenedComputes = flatten(inlinedComputes)
    println("FLATTENED")
    printComputes(flattenedComputes)
    val inlinedComputes2 = performInlining(flattenedComputes)
    println("INLINE2")
    printComputes(inlinedComputes2)

    val rootKey = inlinedComputes2.key
    val basicBlocks = getBasicBlocks(inlinedComputes2)

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
    printComputes(inlinedComputes2)
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

  implicit class ComputesTuple2[T1 : Type, T2 : Type](val tuple : (Computes[T1],Computes[T2])) extends Computable[(T1,T2)] {

    def toComputesSeq = Seq(tuple._1, tuple._2)
    def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit opCtx : OpContext, keyCts : KeyContext) = seq match {
      case Seq(left : Computes[T1], right : Computes[T2]) => ComputesTuple2((left, right))
    }

    def tryFold(implicit opCts : OpContext, keyCtx : KeyContext) = None

    def flatten = {
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

