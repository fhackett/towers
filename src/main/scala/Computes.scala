package towers.computes

import Predef.{any2stringadd => _, _} // allow implicits to override +

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}
import scala.collection.{Set,Map}
import scala.collection.immutable.TreeSet

import quoted._
import tasty._

type ComputesKey = Int
val NoKey = -1

trait KeyContext {
  def getKeyOf(obj : AnyRef) : ComputesKey
}

trait OpContext {
  def resolve[T](computes : Computes[T])(implicit keyCtx : KeyContext) : Computes[T]
}

sealed abstract class Computes[T] {
  def tType : Type[T]

  private val k1 = new AnyRef
  private val k2 = new AnyRef
  def key(implicit keyCtx : KeyContext) = keyCtx.getKeyOf(k1)
  def auxKey(implicit keyCtx : KeyContext) = keyCtx.getKeyOf(k2)
  def auxVar : ComputesVar[T]

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) : Computes[T]
  def toComputesSeq : Seq[Computes[_]]

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) : Option[Computes[T]]
}

abstract class Computable[T : Type] given QuoteContext extends Computes[T] {
  val tType = implicitly[Type[T]]
  // translate this Computable into some lower-level implementation
  def flatten : Computes[T]

  val auxVar = ComputesVar[T]()

  //val foldUnderstands : List[ClassTag[Computes[T]]]
  //val flattenProduces : ClassTag[Computes[T]]
}

final class ComputesVar[T : Type]() given QuoteContext extends Computes[T] {
  val tType = implicitly[Type[T]]
  val auxVar = this
  
  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = ???
  def toComputesSeq = Seq.empty
  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
}

final class ComputesIndirect[T](var binding : Computes[T]) given QuoteContext extends Computes[T] {
  def tType = binding.tType
  def auxVar = binding.auxVar

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = ???
  def toComputesSeq =
    if binding != null then {
      Seq(binding)
    } else {
      Seq.empty
    }

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = ???
}

final class ComputesBinding[V, T : Type](val name : ComputesVar[V], val value : Computes[V], val body : Computes[T]) given QuoteContext extends Computes[T] {
  val tType = implicitly[Type[T]]
  val auxVar = ComputesVar[T]()

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = ???
  def toComputesSeq = Seq(value, body)

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = ???
}

final class ComputesExpr[T : Type](val parameters : Seq[Computes[_]], val exprFn : Seq[Expr[_]] => Expr[T]) given QuoteContext extends Computes[T] {
  val tType = implicitly[Type[T]]
  val auxVar = ComputesVar[T]()

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = ComputesExpr(seq, exprFn)
  def toComputesSeq = parameters
  
  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
}

final class ComputesApplication[FnType <: Computes.==>[_,Result], Result : Type](val arguments : Seq[Computes[_]], val function : Computes[FnType]) given QuoteContext extends Computes[Result] {
  val tType = implicitly[Type[Result]]
  val auxVar = ComputesVar[Result]()

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = seq match {
    case Seq(function : Computes[FnType], arguments :_*) => ComputesApplication(arguments.asInstanceOf[Seq[Computes[_]]], function)
  }
  def toComputesSeq = function +: arguments

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
}

class ComputesLazyRef[T](ref : given QuoteContext => Computes[T]) extends Computes[T] {
  def tType = ??? // see below
  def auxVar = ??? // I could implement this, but it's needlessly complicated and no-one should ever be referencing it
  def computes given QuoteContext : Computes[T] = ref

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = ???
  def toComputesSeq = ???

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
}

class ComputesFunction[FnType <: Computes.==>[_,Result] : Type, Result : Type](val inst : Computes.FnInst[FnType], val parameters : Seq[ComputesVar[_]], val body : Computes[Result]) given QuoteContext extends Computes[FnType] {
  val tType = implicitly[Type[FnType]]
  val auxVar = ComputesVar[FnType]()

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = ???
  def toComputesSeq = Seq(body)

  def tryFold(implicit opCts : OpContext, keyCtx : KeyContext) = None
}

final class ComputesSwitch[Arg, Result : Type](
  val argument : Computes[Arg],
  val cases : Seq[(Computes[Arg],Computes[Result])],
  val default : Option[Computes[Result]]
) given QuoteContext extends Computes[Result] {
  val tType = implicitly[Type[Result]]
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

  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) =
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
    def apply(pc : Expr[Int], closure : Expr[Array[Any]]) given QuoteContext : Expr[F]
  }

  implicit def Inst_==>[A <: Tuple,R] : FnInst[A==>R] = new {
    def apply(pc : Expr[Int], closure : Expr[Array[Any]]) given QuoteContext = '{ ==>(${ pc }, ${ closure }) }
  }

  type |=>[-Args, +Result] = Tuple1[Args]==>Result

  implicit def freshVar[T : Type] given QuoteContext : ComputesVar[T] = ComputesVar[T]()

  def C[T](computes : given QuoteContext => Computes[T]) : Computes[T] = ref(computes)
  def ref[T](computes : given QuoteContext => Computes[T]) : Computes[T] = ComputesLazyRef(computes)

  implicit class ComputesFunction1[
    Arg1 : Type,
    Result : Type,
    F <: Arg1|=>Result : Type](
      fn : Computes[Arg1] => Computes[Result]
    )(implicit
      inst : FnInst[F],
      qctx : QuoteContext,
      arg1 : ComputesVar[Arg1]
    ) extends ComputesFunction[F,Result](inst, List(arg1), fn(arg1))

  implicit class ComputesFunction2[
    Arg1 : Type, Arg2 : Type,
    Result : Type,
    F <: (Arg1,Arg2)==>Result : Type](
      fn : (Computes[Arg1], Computes[Arg2]) => Computes[Result]
    )(implicit
      inst : FnInst[F],
      qctx : QuoteContext,
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
      qctx : QuoteContext,
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
      qctx : QuoteContext,
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
      qctx : QuoteContext,
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
      (fn : =>Computes[F]) given QuoteContext {
    def apply(arg1 : Computes[Arg1]) : Computes[Result] = ComputesApplication(List(arg1), ref(fn))
  }

  implicit class ComputesApplication2[
      Arg1 : Type, Arg2 : Type,
      Result : Type,
      F <: (Arg1,Arg2)==>Result : Type]
      (fn : =>Computes[F]) given QuoteContext {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2]) : Computes[Result] = ComputesApplication(List(arg1, arg2), ref(fn))
  }

  implicit class ComputesApplication3[
      Arg1 : Type, Arg2 : Type, Arg3 : Type,
      Result : Type,
      F <: (Arg1,Arg2,Arg3)==>Result : Type]
      (fn : =>Computes[F]) given QuoteContext {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2], arg3 : Computes[Arg3]) : Computes[Result] =
      ComputesApplication(List(arg1, arg2, arg3), ref(fn))
  }

  implicit class ComputesApplication4[
      Arg1 : Type, Arg2 : Type, Arg3 : Type, Arg4 : Type,
      Result : Type,
      F <: (Arg1,Arg2,Arg3,Arg4)==>Result : Type]
      (fn : =>Computes[F]) given QuoteContext {
    def apply(arg1 : Computes[Arg1], arg2 : Computes[Arg2], arg3 : Computes[Arg3], arg4 : Computes[Arg4]) : Computes[Result] =
      ComputesApplication(List(arg1, arg2, arg3, arg4), ref(fn))
  }

  implicit class ComputesApplication5[
      Arg1 : Type, Arg2 : Type, Arg3 : Type, Arg4 : Type, Arg5 : Type,
      Result : Type,
      F <: (Arg1,Arg2,Arg3,Arg4,Arg5)==>Result : Type]
      (fn : =>Computes[F]) given QuoteContext {
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

  trait RewriteAction {
    def apply[T](computes : Computes[T])(implicit opCtx : OpContext) : Option[Computes[T]]
  }

  def rewrite[T](computes : Computes[T], action : RewriteAction)(implicit keyCtx : KeyContext, qctx : QuoteContext) : Computes[T] = {

    // this is the context in which impl operates
    final case class InCtx(
      // things that should be substituted with a known value (and OutCtx) rather than reprocessed
      val substitutions : Map[ComputesKey,(Computes[_],OutCtx)],
      val known : Map[ComputesKey,Computes[_]],
      val touched : Set[ComputesKey]
    )

    object InCtx {
      def empty = InCtx(
        substitutions=Map.empty,
        known=Map.empty,
        touched=Set.empty)
    }

    final case class OutCtx(
      val isRecursive : Set[Computes[_]],
      val isReferenced : Set[ComputesKey],
      val touched : Set[ComputesKey]
    ) {
      def merge(other : OutCtx) : OutCtx =
        OutCtx(
          isRecursive=isRecursive ++ other.isRecursive,
          isReferenced=isReferenced ++ other.isReferenced,
          touched=touched ++ other.touched)
    }

    object OutCtx {
      def empty =
        OutCtx(
          isRecursive=Set.empty,
          isReferenced=Set.empty,
          touched=Set.empty)
    }

    def injectIndirects[T](computes : Computes[T], indirects : Map[ComputesKey,ComputesIndirect[_]], touched : Set[ComputesKey]) given QuoteContext : (Computes[T], Set[Computes[_]]) =
      if touched(computes.key) then {
        // if already processed, do nothing and just forward it back
        // invariant: either this is a vanilla tree so no indirects are processed at all, or this is after a rewrite where only new cycles may
        // be discovered; old cycles will be touched
        (computes, Set.empty)
      } else if indirects.contains(computes.key) then {
        println(s"I ${computes.key} $computes")
        val indirect = indirects(computes.key).asInstanceOf[ComputesIndirect[T]]
        Predef.assert(indirect.binding == null)
        (indirect, Set(indirect))
      } else {
        println(s"IND REACH ${computes.key} ${computes}")
        computes match {
          case c : ComputesIndirect[T] => {
            Predef.assert(c.binding != null) // you should never reach a null indirect - those should always be in substitutions
            val newInd = ComputesIndirect[T](null)
            val oldBinding = c.binding
            // (temporarily) set the binding to null to ensure there is no way to follow the cycle from inside the cycle
            c.binding = null
            
            val (newBind, isRecursive) = injectIndirects(oldBinding, indirects + ((c.key, newInd)), touched)
            newInd.binding = newBind
            c.binding = oldBinding

            // if somehow an indirect does not contain any back-references, remove the indirect
            if !isRecursive(c) then {
              (newBind, isRecursive)
            } else {
              (newInd, isRecursive)
            }
          }
          case _ => {
            val indirect = ComputesIndirect[T](null)
            val innerIndirects = indirects + ((computes.key, indirect))
            
            val (result, isRecursive) = computes match {
              case c : ComputesLazyRef[T] =>
                injectIndirects(c.computes, innerIndirects, touched)
              case c : ComputesVar[T] =>
                (c, Set.empty : Set[Computes[_]])
              case c : ComputesFunction[fn,r] => {
                val (body, isRec) = injectIndirects(c.body, innerIndirects, touched)
                type f <: _ ==> r
                val result = (ComputesFunction[f,r](
                  c.inst.asInstanceOf[FnInst[f]],
                  c.parameters,
                  body
                ) given (c.tType.asInstanceOf[Type[f]], c.body.tType, the[QuoteContext])).asInstanceOf[Computes[T]]
                (result, isRec : Set[Computes[_]])
              }
              case c : ComputesBinding[v,T] => {
                val (value, vIsRec) = injectIndirects(c.value, innerIndirects, touched)
                val (body, bIsRec) = injectIndirects(c.body, innerIndirects, touched)
                (
                  ComputesBinding(c.name, value, body) given (c.tType, the[QuoteContext]),
                  vIsRec ++ bIsRec : Set[Computes[_]])
              }
              case c => {
                val seq = computes.toComputesSeq
                val (mapped, isRecursives) = seq.map(injectIndirects(_, innerIndirects, touched)).unzip
                val isRecursive = isRecursives.foldLeft(Set.empty : Set[Computes[_]])(_++_)
                (computes.likeFromSeq(mapped), isRecursive : Set[Computes[_]])
              }
            }

            // if back-references were constructed with indirect, this must be the "top" of a cycle so inject indirect into the program
            // otherwise we discard indirect and never speak of it again (since it is neither referenced nor needed)
            if isRecursive(indirect) then { 
              indirect.binding = result
              (indirect, isRecursive)
            } else {
              (result, isRecursive)
            }
          }
        }
      }

    def impl[T](computes : Computes[T], inCtx : InCtx) : (Computes[T],OutCtx) = {
      //println(s"K ${computes.key} $computes $inCtx")
      /*println(s"REACH ${computes.key} $computes")
      println(inCtx.substitutions)
      println("SUBSTITUTIONS:")
      for((k,(v,oCtx)) <- inCtx.substitutions) {
        println(s"$k ${v.key} $oCtx")
      }
      println(inCtx.known)
      println(s"TOUCHED: ${inCtx.touched}")
      printComputes(computes)*/

      // this is the general case - it is referenced in two places so it is its own function
      def generalProc[T](computes : Computes[T], inCtx : InCtx) : (Computes[T],OutCtx) = {
        val seq = computes.toComputesSeq
        val (mapped, outCtxs) = seq.map(impl(_, inCtx)).unzip
        val outCtx = outCtxs.foldLeft(OutCtx.empty)(_.merge(_))

        val beforeAction = computes.likeFromSeq(mapped)

        implicit val opCtx : OpContext = new {
          def resolve[T](computes : Computes[T])(implicit keyCtx : KeyContext) : Computes[T] =
            inCtx.known.getOrElse(computes.key, computes).asInstanceOf[Computes[T]]
        }
        
        action(beforeAction) match {
          case Some(f) => {
            // reprocess the action result, adding all of outCtx.touched to inCtx.touched so we don't reprocess anything
            // we've already seen before. This should specifically recurse over only new nodes.
            val inCtx2 = inCtx.copy(touched=inCtx.touched ++ outCtx.touched)
            val (fWithRedirects, _) = injectIndirects(f, Map.empty, inCtx2.touched)
            val (result, nestedOutCtx) = impl(fWithRedirects, inCtx2)
            // FIXME: ensure OutCtx contains correct isReferenced and isRecursive info, or we start deleting Binding and Indirect we actually
            // needed
            (result, nestedOutCtx.copy(
              touched=nestedOutCtx.touched ++ outCtx.touched))
          }
          case None => (beforeAction, outCtx)
        }
      }

      if inCtx.substitutions.contains(computes.key) then {
        //println("SUB ${computes.key} -> ${inCtx.substitutions(computes.key).key}")
        inCtx.substitutions(computes.key).asInstanceOf[(Computes[T],OutCtx)] match {
          case (c : ComputesIndirect[T], outCtx) =>
            Predef.assert(outCtx == null)
            Predef.assert(c.binding == null)
            // ignoring outCtx here will only matter if a var is referenced above its own declaration
            // which is wrong anyway, and can only happen with unsound mutually referential ASTs
            (c, OutCtx(
              isRecursive=Set(c),
              isReferenced=Set.empty,
              touched=Set(c.key)))
          case (c, outCtx) =>
            (c, outCtx)
        }
      } else if inCtx.touched(computes.key) then {
        // if already processed, do nothing and just forward it back
        println(s"TOUCHED! ${computes.key}")
        (computes, OutCtx(
          isRecursive=Set.empty,
          isReferenced=Set.empty,
          touched=Set.empty))
      } else {
        computes match {
          case c : ComputesIndirect[T] => {
            Predef.assert(c.binding != null) // you should never reach a null indirect - those should always be in substitutions
            val newInd = ComputesIndirect[T](null)
            val oldBinding = c.binding
            // (temporarily) set the binding to null to ensure there is no way to follow the cycle from inside the cycle
            c.binding = null
            
            val (newBind, outCtx) = impl(oldBinding, inCtx.copy(substitutions=inCtx.substitutions + ((c.key, (newInd,null)))))
            newInd.binding = newBind
            c.binding = oldBinding

            // if somehow an indirect does not contain any back-references, remove the indirect
            if !outCtx.isRecursive(c) then {
              (newBind, outCtx)
            } else {
              (newInd, outCtx.copy(touched=outCtx.touched + newInd.key))
            }
          }
          case _ => {

            def resolve[T](computes : Computes[T]) : Computes[T] = {
              var c = if inCtx.substitutions.contains(computes.key) then {
                inCtx.substitutions(computes.key)._1.asInstanceOf[Computes[T]]
              } else {
                computes
              }
              while (inCtx.known.contains(c.key)) {
                c = inCtx.known(c.key).asInstanceOf[Computes[T]]
              }
              c
            }
            
            val (result, outCtx) = computes match {
              case c : ComputesLazyRef[T] =>
                ??? // unreachable, should be replaced with an indirect by injectIndirects
              case c : ComputesVar[T] =>
                // only reached when re-processing a subtree that has already been processed,
                // but part of it needs reprocessing due to a rewrite (i.e the body of an already
                // processed function literal)
                (c, OutCtx(
                  isRecursive=Set.empty,
                  isReferenced=Set(c.key),
                  touched=Set(c.key)))
              case c : ComputesApplication[fn,T] => {
                resolve(c.function) match {
                  case f : ComputesFunction[fn, T] => {
                    //println(s"INLINE ${c.function.key} -> ${fNonDup.key}")

                    val pKeys = f.parameters.map(_.key)

                    // bind all the arguments so they process left to right
                    val inlined = (f.parameters zip c.arguments).foldRight(f.body)({
                      case ((name : ComputesVar[t], value), body) =>
                        // these two types should be the same, and this convinces the type system this is so
                        type VT = t
                        implicit val e1 = body.tType
                        value match {
                          case v : Computes[VT] =>
                            ComputesBinding[t, T](name, v, body)
                        }
                    })

                    // process the result via the Binding case, allowing for things like arguments never being referenced
                    // and being accessed and inlined via InCtx.known, etc...
                    impl(inlined, inCtx)
                  }
                  case _ => {
                    generalProc(c, inCtx) // if you can't inline, just give up and process c the generic way
                  }
                }
              }
              case c : ComputesFunction[fn,r] => {
                val pKeys = c.parameters.map(_.key)
                val newParams = c.parameters.map({
                  case v : ComputesVar[v] =>
                    ComputesVar[v]() given (v.tType, the[QuoteContext])
                })
                val newParamPairs = newParams zip (newParams.map(v =>
                    OutCtx(
                      isRecursive=Set.empty,
                      isReferenced=Set(v.key),
                      touched=Set(v.key))))

                val (body, outCtx) = impl(c.body, inCtx.copy(substitutions=inCtx.substitutions ++ (pKeys zip newParamPairs)))
                type f <: _ ==> r
                val result = (ComputesFunction[f,r](
                  c.inst.asInstanceOf[FnInst[f]],
                  newParams,
                  body) given (c.tType.asInstanceOf[Type[f]], c.body.tType, the[QuoteContext])).asInstanceOf[Computes[T]]
                (result, outCtx)
              }
              case c : ComputesBinding[v,T] => {
                val newBind = ComputesVar[v]() given (c.name.tType, the[QuoteContext])
                val (value, vOutCtx) = impl(c.value, inCtx)
                
                //println(s"KNOW ${newBind.key} (${c.name.key}) -> ${value.key} (${c.value.key}})")

                val (body, bOutCtx) = impl(
                  c.body,
                  inCtx.copy(
                    substitutions=inCtx.substitutions + ((c.name.key, (newBind, OutCtx(
                      isRecursive=Set.empty,
                      isReferenced=Set(newBind.key),
                      touched=Set(newBind.key))))),
                    known=inCtx.known + ((newBind.key, value))))

                // if the body contains no references to newBind, it means value is not needed and we can completely elide this binding
                if bOutCtx.isReferenced(newBind.key) then {
                  (
                    ComputesBinding(newBind, value, body) given (c.tType, the[QuoteContext]),
                    vOutCtx.merge(bOutCtx))
                } else {
                  (body, bOutCtx)
                }
              }
              case c => generalProc(c, inCtx) 
            }

            // add the result to touched
            (result, outCtx.copy(touched=outCtx.touched + result.key))
          }
        }
      }
    }

    val (withIndirects, _) = injectIndirects(computes, Map.empty, Set.empty)
    println("WITHINDIRECTS")
    printComputes(withIndirects)
    val (result, _) = impl(withIndirects, InCtx.empty)
    //println("REWRITE")
    //printComputes(result)
    result
  }

  def performInlining[T](computes : Computes[T]) given KeyContext, QuoteContext : Computes[T] =
    rewrite(computes, new {
      def apply[T](computes : Computes[T])(implicit opCtx : OpContext) : Option[Computes[T]] =
        computes.tryFold
    })

  def flatten[T](computes : Computes[T]) given KeyContext, QuoteContext : Computes[T] =
    rewrite(computes, new {
      def apply[T](computes : Computes[T])(implicit opCtx : OpContext) : Option[Computes[T]] =
        computes match {
          case c : Computable[T] => Some(c.flatten)
          case c => None
        }
    })

  abstract class BasicBlock {
    def apply(pcMap : Map[ComputesKey,Int], vMap : Map[ComputesKey,Expr[_]], popData : Expr[Any], pushData : Expr[Any]=>Expr[Unit], pushPC : Expr[Int]=>Expr[Unit]) given QuoteContext : Expr[Unit]
  }
  abstract class Continuation[T] {
    def apply(value : Expr[T], pcMap : Map[ComputesKey,Int], vMap : Map[ComputesKey,Expr[_]], popData : Expr[Any], pushData : Expr[Any]=>Expr[Unit], pushPC : Expr[Int]=>Expr[Unit]) given QuoteContext : Expr[Unit]
  }

  class BlockGen given (qctx_ : QuoteContext) {
    private val statements = ArrayBuffer[qctx.tasty.Statement]()
    private val bindings = HashMap[ComputesKey,Expr[_]]()
    
    val qctx = qctx_

    def bind[T](name : ComputesVar[T], gen : given QuoteContext => Expr[T]) given KeyContext : BlockGen = {
      import qctx.tasty._
      val expr : Expr[T] = gen
      implicit val e1 = name.tType
      val bloodSacrifice = '{
        val bind : T = ${ expr }
        bind
      }

      bloodSacrifice.unseal match {
        case IsInlined(inl) => inl.body match {
          case IsBlock(b) => {
            statements ++= b.statements
            bindings(name.key) = b.expr.seal.cast[T]
          }
        }
      }
      this
    }

    def statement(gen : given QuoteContext => Expr[Unit]) given KeyContext : BlockGen = {
      import qctx.tasty._
      val expr : Expr[Unit] = gen
      val bloodSacrifice = '{
        ${ expr }
        ()
      }

      bloodSacrifice.unseal match {
        case IsInlined(inl) => inl.body match {
          case IsBlock(b) => {
            statements ++= b.statements
          }
        }
      }
      this
    }

    def byName[T](name : ComputesVar[T]) given KeyContext : Expr[T] =
      bindings(name.key).asInstanceOf[Expr[T]]

    def getBlock() : Expr[Unit] = {
      import qctx.tasty._
      Block(
        statements.toList,
        Literal(Constant(()))).seal.cast[Unit]
    }

    def getBlockWithResult[T : Type](result : given QuoteContext => Expr[T]) : Expr[T] = {
      import qctx.tasty._
      Block(statements.toList, result.unseal).seal.cast[T]
    }
  }

  object BlockGen {
    def apply() given QuoteContext = new BlockGen()

    def apply(parent : BlockGen) : BlockGen = {
      val blockGen = new BlockGen() given parent.qctx
      blockGen.bindings ++= parent.bindings
      blockGen
    }
  }

  def printComputes[T](computes : Computes[T])(implicit keyCtx : KeyContext) : Unit = {
    
    val visitedSet = HashSet[ComputesKey]()

    var indentation = 0

    def line(str : String) : Unit = {
      for(i <- 0 until indentation) {
        print("  ")
      }
      println(str)
    }

    def impl[T](computes : Computes[T]) : Unit = {
      if computes != null then {
        if visitedSet.contains(computes.key) then {
          line(s"<> ${computes.key}")
        } else {
          visitedSet += computes.key
          computes match {
            case c : ComputesFunction[_,_] => {
              line(s"${c.key}(${c.parameters.map(_.key)}){")
              indentation += 1
              impl(c.body)
              indentation -= 1
              line("}")
            }
            case c : ComputesVar[_] => {
              line(s"${c.key}")
            }
            case c : ComputesBinding[_,_] => {
              line(s"${c.name.key} = [[${c.key}]] ")
              indentation += 1
              impl(c.value)
              indentation -= 1
              line("; {")
              impl(c.body)
              line("}")
            }
            case c : ComputesApplication[_,_] => {
              impl(c.function)
              line(s"( [[${c.key}]]")
              indentation += 1
              for(arg <- c.arguments) {
                impl(arg)
              }
              indentation -= 1
              line(")")
            }
            case c : ComputesLazyRef[T] => {
              println(s"${c.key} :: LAZY")
            }
            case c : ComputesIndirect[T] => {
              line(s"${c.key} => ")
              indentation += 1
              impl(c.binding)
              indentation -= 1
            }
            case c => {
              line(s"?? ${c.key} $c")
              indentation += 1
              for(part <- c.toComputesSeq) {
                impl(part)
              }
              indentation -= 1
            }
          }
        }
      } else {
        println("NULL")
      }
    }

    impl(computes)
  }

  def reifyCall[A1 : Type, R : Type](computes : Computes[A1|=>R], a1 : Expr[A1])
                                    (implicit qctx : QuoteContext) = {
    reify(computes(expr((), _ => a1)))
  }

  def reify[T : Type](computes : Computes[T])(implicit qctx: QuoteContext) = {
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

    val nodeClosures = HashMap[ComputesKey,TreeSet[ComputesKey]]()
    val vNodes = HashMap[ComputesKey,ComputesVar[_]]()
    ;{

      def makePass[T](computes : Computes[T]) : Unit = {
        val visitedSet = HashSet[ComputesKey]()
        def impl[T](computes : Computes[T]) : TreeSet[ComputesKey] = {
          if visitedSet(computes.key) then {
            nodeClosures.getOrElse(computes.key, TreeSet.empty)
          } else {
            visitedSet += computes.key
            val result = computes match {
              case c : ComputesIndirect[T] => impl(c.binding)
              case c : ComputesVar[T] => {
                vNodes(c.key) = c
                TreeSet(c.key)
              }
              case c : ComputesBinding[_,T] =>
                impl(c.value) ++ (impl(c.body) - c.name.key)
              case c : ComputesFunction[_,T] =>
                impl(c.body) -- c.parameters.map(v => v.key)
              case c =>
                c.toComputesSeq.foldLeft(TreeSet.empty : TreeSet[ComputesKey])(_ ++ impl(_))
            }
            nodeClosures(computes.key) = result ++ nodeClosures.getOrElse(computes.key, TreeSet.empty : TreeSet[ComputesKey])
            result
          }
        }
        impl(computes)
      }
      // 2 passes : one to follow all the paths, and one to propagate the results from
      // the back-references
      makePass(inlinedComputes2)
      makePass(inlinedComputes2)
    }

    val rootBlock = BlockGen()
    val PC_STACK = ComputesVar[ArrayStack[Int]]()
    val DATA_STACK = ComputesVar[ArrayStack[Any]]()
    rootBlock.bind(PC_STACK, '{ ArrayStack[Int]() })
    rootBlock.bind(DATA_STACK, '{ ArrayStack[Any]() })

    def pushPC(pc : Expr[Int]) given QuoteContext : Expr[Unit] =
      '{ ${ rootBlock.byName(PC_STACK) }.push(${ pc }) }
    def popData[T : Type] given QuoteContext : Expr[T] =
      '{ ${ rootBlock.byName(DATA_STACK) }.pop.asInstanceOf[T] }
    def pushData(data : Expr[Any]) given QuoteContext : Expr[Unit] =
      '{ ${ rootBlock.byName(DATA_STACK) }.push(${ data }) }

    val pcMap = HashMap[ComputesKey,Int]()
    var nextPC = 0
    def getPC(key : ComputesKey) : Int = {
      val pc = pcMap.getOrElseUpdate(key, {
        val pc = nextPC
        nextPC += 1
        pc
      })
      println(s"getPC $key -> $pc")
      pc
    }
    val blockMap = collection.mutable.TreeMap[ComputesKey,Expr[Unit]]()

    type Continuation[T] = (Expr[T],BlockGen)=>Unit

    def bindAuxSet(set : List[Computes[_]], toPreserve : TreeSet[ComputesKey], blockGen : BlockGen, cont : Continuation[Unit]) : Unit =
      set match {
        case hd :: tl =>
          impl(hd, toPreserve ++ tl.flatMap(v => nodeClosures(v.key)), blockGen, (v, blockGen) => {
            blockGen.bind(hd.auxVar, v)
            vNodes(hd.auxVar.key) = hd.auxVar
            bindAuxSet(tl, toPreserve + hd.auxVar.key, blockGen, cont)
          })
        case Nil =>
          cont('{ () }, blockGen)
      }

    def pushArguments(args : List[Computes[_]], toPreserve : TreeSet[ComputesKey], blockGen : BlockGen) : Unit =
      args match {
        case hd :: Nil =>
          impl(hd, toPreserve, blockGen, null)
        case hd :: tl =>
          impl(hd, toPreserve ++ tl.flatMap(v => nodeClosures(v.key)), blockGen, (v, blockGen) => {
            blockGen.statement({ pushData(v) })
            pushArguments(tl, toPreserve, blockGen)
          })
        case Nil => ()
      }

    def pushPreserves(blockGen : BlockGen, toPreserve : TreeSet[ComputesKey]) : Unit = {
      println(s"PUSH $toPreserve $vNodes")
      toPreserve.foreach(k =>
        blockGen.statement({ pushData(blockGen.byName(vNodes(k))) }))
    }

    def popPreserves(blockGen : BlockGen, toPreserve : TreeSet[ComputesKey]) : Unit = {
      println(s"POP $toPreserve")
      toPreserve.toSeq.reverse.foreach(k => {
        vNodes(k) match {
          case v : ComputesVar[t] => {
            implicit val vT = v.tType
            blockGen.bind(v, { popData[t] })
          }
        }
      })
    }
    
    def impl[T](computes : Computes[T], toPreserve : TreeSet[ComputesKey], blockGen : BlockGen, cont : Continuation[T]) : Unit = {
      println(s"REACH ${computes.key} $computes ${nodeClosures(computes.key)}")
      implicit val tType = computes.tType
      computes match {
        case c : ComputesIndirect[T] =>
          c.binding match {
            case b : ComputesFunction[_,T] =>
              impl(b, toPreserve, blockGen, cont)
            case _ => {
              if !blockMap.contains(c.key) then {
                blockMap(c.key) = null // avoid reentrancy problems

                val indBlockGen = BlockGen()
                popPreserves(indBlockGen, nodeClosures(c.key))
                impl(c.binding, TreeSet.empty, indBlockGen, null)

                blockMap(c.key) = indBlockGen.getBlock()
              }

              if cont != null then {
                val contTmp = ComputesVar[Any]()
                blockGen.statement({ pushPC(getPC(contTmp.key).toExpr) })
                pushPreserves(blockGen, toPreserve)

                val contBlockGen = BlockGen()
                contBlockGen.bind(c.auxVar, { popData[T] })
                popPreserves(contBlockGen, toPreserve)
                cont(contBlockGen.byName(c.auxVar), contBlockGen)

                blockMap(contTmp.key) = contBlockGen.getBlock()
              }

              blockGen.statement({ pushPC(getPC(c.key).toExpr) })
              pushPreserves(blockGen, nodeClosures(c.key))
            }
          }
        case c : ComputesVar[T] =>
          if cont != null then {
            cont(blockGen.byName(c), blockGen)
          } else {
            blockGen.statement({ pushData(blockGen.byName(c)) })
          }
        case c : ComputesApplication[fnType,T] => {
          if cont != null then {
            val contTmp = ComputesVar[Any]()
            // push the continuation here, so as to minimise the amount of closure info we push while processing args
            pushPreserves(blockGen, toPreserve)
            blockGen.statement({ pushPC(getPC(contTmp.key).toExpr) })

            val contBlockGen = BlockGen()
            contBlockGen.bind(c.auxVar, { popData[T] })
            popPreserves(contBlockGen, toPreserve)
            cont(contBlockGen.byName(c.auxVar), contBlockGen)

            blockMap(contTmp.key) = contBlockGen.getBlock()
          }
          implicit val e1 = c.function.tType
          impl(c.function, TreeSet.empty ++ c.arguments.flatMap(a => nodeClosures(a.key)), blockGen, (fn, blockGen) => {
            blockGen.statement({ pushPC('{ ${ fn }.pc }) })
            blockGen.statement({ pushData('{ ${ fn }.closure }) })
            pushArguments(c.arguments.toList, toPreserve, blockGen)
          })
        }
        case c : ComputesFunction[T,r] => {
          if !blockMap.contains(c.key) then {
            blockMap(c.key) = null // protect against reentrant situations

            val fnBlockGen = BlockGen()
            c.parameters.toSeq.reverse.foreach({
              case p : ComputesVar[t] => {
                implicit val tt = p.tType
                fnBlockGen.bind(p, { popData[t] })
              }
            })
            val closureTmp = ComputesVar[Array[Any]]()
            fnBlockGen.bind(closureTmp, { popData[Array[Any]] })
            nodeClosures(c.key).zipWithIndex.foreach({
              case (k, i) => {
                val v = vNodes(k)
                fnBlockGen.bind(v, '{ ${ fnBlockGen.byName(closureTmp) }.apply(${ i.toExpr }).asInstanceOf[${v.tType}] })
              }
            })
            impl(c.body, TreeSet.empty, fnBlockGen, null)

            blockMap(c.key) = fnBlockGen.getBlock()
          }

          val closure = nodeClosures(c.key)
          val closureTmp = ComputesVar[Array[Any]]()
          if closure.isEmpty then {
            blockGen.bind(closureTmp, '{ null })
          } else {
            blockGen.bind(closureTmp, '{ Array[Any]() })
            closure.zipWithIndex.foreach({
              case (k, i) => {
                val v = vNodes(k)
                blockGen.statement('{ ${ blockGen.byName(closureTmp) }(${ i.toExpr }) = ${ blockGen.byName(vNodes(k)) } })
              }
            })
          }
          val fnTmp = ComputesVar[T]()
          blockGen.bind(fnTmp, c.inst(getPC(c.key).toExpr, blockGen.byName(closureTmp)))
          if cont != null then {
            cont(blockGen.byName(fnTmp), blockGen)
          } else {
            blockGen.statement({ pushData(blockGen.byName(fnTmp)) })
          }
        }
        case c : ComputesBinding[vT,T] =>
          impl(c.value, toPreserve ++ nodeClosures(c.body.key) - c.name.key, blockGen, (v, blockGen) => {
            blockGen.bind(c.name, v)
            impl(c.body, toPreserve, blockGen, cont)
          })
        case c : ComputesSwitch[argT,T] => {
          var contTmp = ComputesVar[Any]()
          if cont != null then {
            pushPreserves(blockGen, toPreserve)
            blockGen.statement({ pushPC(getPC(contTmp.key).toExpr) })

            val contBlockGen = BlockGen()
            contBlockGen.bind(c.auxVar, { popData[T] })
            popPreserves(contBlockGen, toPreserve)
            cont(contBlockGen.byName(c.auxVar), contBlockGen)

            blockMap(contTmp.key) = contBlockGen.getBlock()
          }
          bindAuxSet(c.argument :: c.cases.map(_._1).toList, TreeSet.empty ++ c.cases.map(_._2).flatMap(r => nodeClosures(r.key)), blockGen, (unit, blockGen) => {
            blockGen.statement(given (qctx : QuoteContext) => {
              import qctx.tasty._
              implicit val e1 = c.argument.tType

              Match(
                blockGen.byName(c.argument.auxVar).unseal,
                (for((v,r) <- c.cases)
                  yield {
                    val bodyBlockGen = BlockGen(blockGen)
                    impl(r, TreeSet.empty, bodyBlockGen, null)

                    val tType = c.argument.tType
                    val bloodSacrifice = '{
                      ??? : Any match {
                        case x if x == ${ bodyBlockGen.byName(v.auxVar) } => ()
                      }
                    }

                    bloodSacrifice.unseal match {
                      case Inlined(_, _, Match(_, List(CaseDef(pattern, guard, _)))) =>
                        CaseDef(pattern, guard, bodyBlockGen.getBlock().unseal)
                    }


                    /*CaseDef(
                      Pattern.Value(
                        bodyBlockGen.byName(v.auxVar).unseal match {
                          case Typed(term, _) => term
                        }),
                      None,
                      bodyBlockGen.getBlock().unseal)*/
                  }).toList ++
                c.default.map(d =>
                    List({
                      val defaultBlockGen = BlockGen(blockGen)
                      impl(d, TreeSet.empty, defaultBlockGen, null)

                      // hack: steal default branch from donor match expression
                      val bloodSacrifice = '{
                        ${ defaultBlockGen.byName(c.argument.auxVar) } match {
                          case _ => ()
                        }
                      }
                      bloodSacrifice.unseal match {
                        case IsInlined(inl) => inl.body match {
                          case IsMatch(m) => m.cases.head match {
                            case CaseDef(pattern, guard, _) =>
                              CaseDef(pattern, guard, defaultBlockGen.getBlock().unseal)
                          }
                        }
                      }
                    })).getOrElse(Nil)
                ).seal.cast[Unit]
            })
          })
        }
        case c : ComputesExpr[T] =>
          bindAuxSet(c.parameters.toList, toPreserve, blockGen, (unit, blockGen) => {
            val result = c.exprFn(c.parameters.map(arg => blockGen.byName(arg.auxVar)))
            if cont != null then {
              cont(result, blockGen)
            } else {
              blockGen.statement({ pushData(result) })
            }
          })
        case c => {
          println(s"Reached unreachable node during codegen: $c")
          ???
        }
      }
    }

    // compute basic blocks
    ;{
      val blockGen = BlockGen()
      impl(inlinedComputes2, TreeSet.empty, blockGen, null)
      blockMap(rootKey) = blockGen.getBlock()
    }

    println("BLOCKS GENERATED")

    rootBlock.statement({ pushPC(getPC(rootKey).toExpr) })
    rootBlock.statement({
      val qctx = implicitly[QuoteContext]
      import qctx.tasty._
      While(
        '{ !${ rootBlock.byName(PC_STACK) }.isEmpty}.unseal,
        Match(
          '{ ${ rootBlock.byName(PC_STACK) }.pop }.unseal,
          blockMap.map({
            case (key, block) =>
              CaseDef(
                Pattern.Value(Literal(Constant(getPC(key)))),
                None,
                // TODO: split each block into its own method, so we don't hit the method size limit
                '{
                  println(s"PC ${${ getPC(key).toExpr }}")
                  println(s"PC_STACK ${${ rootBlock.byName(PC_STACK) }}")
                  println(s"DATA_STACK ${${ rootBlock.byName(DATA_STACK) }}")
                  ${ block }
                }.unseal)
          }).toList)).seal.cast[Unit]
    })

    val expr = rootBlock.getBlockWithResult[T]({ popData })
    ;{
      import qctx.tasty._
      //println(expr.unseal)
      println(expr.show)
    }
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
  
  implicit class ComputesIntOps(lhs : Computes[Int]) given QuoteContext {
    def +(rhs : Computes[Int]) : Computes[Int] =
      expr((lhs, rhs), t => t match { case (lhs,rhs) => '{ ${ lhs } + ${ rhs } }})
    def -(rhs : Computes[Int]) : Computes[Int] =
      expr((lhs, rhs), t => t match { case (lhs,rhs) => '{ ${ lhs } - ${ rhs } }})
  }

  implicit class ComputesTuple2[T1 : Type, T2 : Type](val tuple : (Computes[T1],Computes[T2])) given QuoteContext extends Computable[(T1,T2)] {

    def toComputesSeq = Seq(tuple._1, tuple._2)
    def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCts : KeyContext) = seq match {
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

  implicit class ComputesTuple2Ops[T1 : Type, T2 : Type](lhs : Computes[(T1,T2)]) given QuoteContext {
    def _1 : Computes[T1] =
      expr1(lhs, lhs => '{ ${ lhs }._1 })
    def _2 : Computes[T2] =
      expr1(lhs, lhs => '{ ${ lhs }._2 })
  }

  implicit class ComputesListOps[T : Type](lhs : Computes[List[T]]) given QuoteContext {
    def isEmpty : Computes[Boolean] =
      expr1(lhs, lhs => '{ ${ lhs }.isEmpty })
    def head : Computes[T] =
      expr1(lhs, lhs => '{ ${ lhs }.head })
    def tail : Computes[List[T]] =
      expr1(lhs, lhs => '{ ${ lhs }.tail })
  }

  implicit class ComputesSwitchOp[Lhs](lhs : Computes[Lhs]) given QuoteContext {
    def switch[Rhs : Type](cases : List[(Computes[Lhs],Computes[Rhs])], default : Computes[Rhs]) : Computes[Rhs] =
      ComputesSwitch(lhs, cases, Some(default))
    def switch[Rhs : Type](cases : List[(Computes[Lhs],Computes[Rhs])]) : Computes[Rhs] =
      ComputesSwitch(lhs, cases, None)
  }

  def let[V : Type,T : Type](value : Computes[V], body : Computes[V|=>T]) given QuoteContext : Computes[T] = body(value)

  def const[T : Type : Liftable](v : T) given QuoteContext : Computes[T] =
    ComputesExpr(Nil, es => v.toExpr)

  type ComputesToExpr[C] = C match { case Computes[t] => Expr[t] }

  /*trait Computes2Expr[In <: Tuple, Out <: Tuple]

  given C2E [T, Tl <: Tuple, Ttl <: Tuple] as Computes2Expr[Computes[T] *: Tl, Expr[T] *: Ttl] given (fTl : Computes2Expr[Tl,Ttl])
  given C2EBase as Computes2Expr[Unit,Unit]*/

  def expr1[T : Type, Param](param : Computes[Param], body : given QuoteContext => Expr[Param] => Expr[T]) given QuoteContext : Computes[T] =
    ComputesExpr(
      List(param),
      exprs => body(exprs.head.asInstanceOf[Expr[Param]]))

  /*def expr[T : Type, Params <: Tuple, EParams <: Tuple](params : Params, body : EParams => Expr[T])
      given Computes2Expr[Params,EParams] : Computes[T] =
    ComputesExpr(
      params.toArray.toList.asInstanceOf[List[Computes[_]]],
      exprs => body(exprs.foldRight(() : Tuple)((hd, tl) => hd *: tl).asInstanceOf[Tuple.Map[Params,ComputesToExpr]]))*/

     def expr[T : Type, Params <: Tuple](params : Params, body : given QuoteContext => Tuple.Map[Params,ComputesToExpr] => Expr[T]) given QuoteContext : Computes[T] =
    ComputesExpr(
      params.toArray.toList.asInstanceOf[List[Computes[_]]],
      exprs => body(exprs.foldRight(() : Tuple)((hd, tl) => hd *: tl).asInstanceOf[Tuple.Map[Params,ComputesToExpr]]))

}

import Computes._

val add1 : Computes[Int|=>Int] = C(
  (i : Computes[Int]) => i+const(1)
)

val add2 : Computes[Int|=>Int] = C(
  (i : Computes[Int]) => add1(add1(i))
)

val countdown : Computes[Int|=>Boolean] = C(
  (i : Computes[Int]) =>
    i.switch(
      List(const(0) -> const(true)),
      default=countdown(i-const(1)))
)

val add1AddedL : Computes[Int|=>Int] = C(
  (i : Computes[Int]) =>
    i + add1(i)
)

val add1AddedR : Computes[Int|=>Int] = C(
  (i : Computes[Int]) =>
    add1(i) + i
)

val unimap : Computes[(List[Int],Int|=>Int)==>List[Int]] = C(
  (list : Computes[List[Int]], fn : Computes[Int|=>Int]) =>
    list.isEmpty.switch(
      List(
        const(true) -> expr((), _ => '{ Nil }),
        const(false) ->
          expr((fn(list.head), unimap(list.tail, fn)),
            tpl => tpl match { case (mhd,mtl) => '{ ${ mhd } :: ${ mtl } } })))
)

val unimap2 : Computes[(List[Int],Int|=>Int)|=>List[Int]] = C(
  (args : Computes[(List[Int],Int|=>Int)]) =>
    let(expr1(args, args => '{ ${ args }._1 }),
      (list : Computes[List[Int]]) =>
        let(expr1(args, args => '{ ${ args }._2 }),
          (fn : Computes[Int|=>Int]) =>
            list.isEmpty.switch(
              List(
                const(true) -> expr((), _ => '{ Nil }),
                const(false) ->
                  expr((fn(list.head), unimap2((list.tail, fn))),
                    tpl => tpl match { case (mhd,mtl) => '{ ${ mhd } :: ${ mtl } } })))))
)

val unimapAdd1 : Computes[List[Int]|=>List[Int]] = C(
  (list : Computes[List[Int]]) =>
    unimap(list, add1)
)

val unimap2Add1 : Computes[List[Int]|=>List[Int]] = C(
  (list : Computes[List[Int]]) =>
    unimap2((list, add1))
)

inline def doAdd1(i : Int) : Int = ${ Computes.reifyCall(add1, '{ i }) }

inline def doAdd2(i : Int) : Int = ${ Computes.reifyCall(add2, '{ i }) }

inline def doCountdown(i : Int) : Boolean = ${ Computes.reifyCall(countdown, '{ i }) }

inline def doAdd1AddedL(i : Int) : Int = ${ Computes.reifyCall(add1AddedL, '{ i }) }

inline def doAdd1AddedR(i : Int) : Int = ${ Computes.reifyCall(add1AddedR, '{ i }) }

inline def doUnimapAdd1(list : List[Int]) : List[Int] = ${ Computes.reifyCall(unimapAdd1, '{ list }) }

inline def doUnimap2Add1(list : List[Int]) : List[Int] = ${ Computes.reifyCall(unimap2Add1, '{ list }) }

