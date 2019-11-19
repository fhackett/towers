package towers

import Predef.{any2stringadd => _, _} // allow implicits to override +

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}
import scala.collection.{Seq}
import scala.collection.immutable.TreeSet

import scala.deriving._
import scala.quoted._
import scala.tasty._
import scala.compiletime._
import scala.reflect._

class ==>[Args <: Tuple, Result](val pc : Int, val closure : Array[Any])

sealed abstract class CHandle[T] {
  val index : Int
  lazy val owner : Computes[_]
}

sealed abstract class Computes[T] {
  val theType : Type[T]
}

object Computes {

  def compile[T : Type](computes : Computes[T])(given qctx : QuoteContext) : Expr[T] = {

    final case class ComputesKey(val i : Int)
    object ComputesKey {
      private var nextKey = 0
      def fresh() : ComputesKey = {
        val k = nextKey
        nextKey += 1
        ComputesKey(k)
      }
    }

    final case class KeyRef[T](val key : ComputesKey) extends Computes[T]

    final case class NameKey(val i : Int)
    object NameKey {
      private var nextKey = 0
      def fresh() : NameKey = {
        val k = nextKey
        nextKey += 1
        NameKey(k)
      }
    }

    sealed abstract class ComputesRecord
    object ComputesRecord {
      //final case class Normal[T](val computes : Computes[T]) extends ComputesRecord
      final case class EnterCycle(val bodyRef : ComputesKey) extends ComputesRecord
      final case class CyclicReference(val backRef : ComputesKey) extends ComputesRecord

      final case class Composite(val rule : Rule, val handles : List[CHandle[_]], val members : List[ComputesKey]) extends ComputesRecord
      final case class Code[T](val fn : List[Expr[_]]=>Expr[T], val args : List[ComputesKey]) extends ComputesRecord
      final case class Application(val fn : ComputesKey, val args : List[ComputesKey]) extends ComputesRecord
      final case class Function(val body : ComputesKey, val args : List[NameKey]) extends ComputesRecord
      final case class NameBinding(val name : NameKey, val value : ComputesKey, val body : ComputesKey) extends ComputesRecord
      final case class NameRef(val name : NameKey) extends ComputesRecord
      final case class Constant[T](val v : T, val liftable : Liftable[T]) extends ComputesRecord
      final case class Branch(val cond : ComputesKey, val t : ComputesKey, val f : ComputesKey) extends ComputesRecord
      final case class DispatchTable[Argument](val input : ComputesKey, val argType : Type[Argument], val argLiftable : Liftable[Argument], val cases : List[(Argument,ComputesKey)], val default : Option[ComputesKey]) extends ComputesRecord
    }
    
    val typeMap = HashMap[ComputesKey,Type[_]]()
    // simulate mutable pointers by having all fields hold keys into a map
    // on rewrite, each field must only be referenced once - check this.
    // have a second map that holds dependency information: for each cell, which rewrite is waiting on it?
    // once we gain knowledge, mutate the affected cells at a distance, recursively performing any changes needed
    val computesMap = HashMap[ComputesKey,ComputesRecord]()

    def readGraph[T](computes : Computes[T], openCycles : Map[Ref[_],ComputesKey], bindings : Map[Name[_],NameKey]) : ComputesKey = computes match {
      case c : Ref[T] => {
        if( openCycles.contains(c) ) {
          val key = ComputesKey.fresh()
          computesMap += ((key, ComputesRecord.CyclicReference(openCycles(c))))
          typeMap += ((key, c.getType))
          key
        } else {
          // ensure all references other than names and cycles are unique by never deduplicating
          val entryKey = ComputesKey.fresh()
          val bodyKey = readGraph(c.ref, openCycles + ((c, entryKey)), bindings)
          computesMap += ((entryKey, ComputesRecord.EnterCycle(entryKey)))
          typeMap += ((entryKey, c.getType))
          entryKey
        }
      }
      case _ => {
        val result : ComputesRecord = computes match {
          case _ : Ref[T] => ??? // handled above
          case Composite(rule, rewrite, lower, members, handles) => ??? // TODO
          case Code(fn, args) => {
            val argKeys = args.map(readGraph(_, openCycles, bindings))
            ComputesRecord.Code(fn, argKeys)
          }
          case Application(fn, args) => {
            val argKeys = args.map(readGraph(_, openCycles, bindings))
            val fnKey = readGraph(fn, openCycles, bindings)
            ComputesRecord.Application(fnKey, argKeys)
          }
          case Function(body, args) => {
            val argKeys = args.map((_, NameKey.fresh()))
            val bodyKey = readGraph(body, openCycles, bindings ++ argKeys)
            ComputesRecord.Function(bodyKey, argKeys.map(_._2))
          }
          case NameBinding(name, value, body) => {
            val nameKey = NameKey.fresh()
            val valueKey = readGraph(value, openCycles, bindings)
            val bodyKey = readGraph(body, openCycles, bindings + ((name, nameKey)))
            ComputesRecord.NameBinding(nameKey, valueKey, bodyKey)
          }
          case c @ Constant(v) => {
            ComputesRecord.Constant(v, c.liftable)
          }
          case Branch(cond, t, f) => {
            val condKey = readGraph(cond, openCycles, bindings)
            val tKey = readGraph(cond, openCycles, bindings)
            val fKey = readGraph(cond, openCycles, bindings)
            ComputesRecord.Branch(condKey, tKey, fKey)
          }
          case d @ DispatchTable(input, pairs, default) => {
            val inputKey = readGraph(input, openCycles, bindings)
            val casePairs = pairs.map({ case (value, result) => (value, readGraph(result, openCycles, bindings))})
            val defaultKey = default.map(readGraph(_, openCycles, bindings))
            ComputesRecord.DispatchTable(inputKey, d.argType, d.argLiftable, casePairs, defaultKey)
          }
          case name : Name[T] => {
            assert(bindings.contains(name))
            ComputesRecord.NameRef(bindings(name))
          }
        }
        val key = ComputesKey.fresh()
        computesMap += ((key, result))
        typeMap += ((key, computes.theType))
        key
      }
    }

    val rootKey = readGraph(computes, Map.empty, Map.empty)

    '{ ??? }
  }

  trait TupleSize[Tpl <: Tuple] {
    val size : Int 
  }

  given TupleSize[Unit] {
    val size = 0
  }

  given [Hd, Tl <: Tuple](given aft : TupleSize[Tl]) : TupleSize[Hd *: Tl] {
    val size = aft.size + 1
  }

  def compileFn[Args <: Tuple : Type, Result : Type]
               (c : Computes[Args==>Result])
               (given qctx : QuoteContext, aft : TupleSize[Args]) : Expr[Args=>Result] = '{
    (args : Args) => {
      val data = args.toIArray
      ${
        compile(c({
          // this is compile-land so we can't ask the runtime tuple its size. Instead, we have the compiler summon it as an implicit
          val tplSize = aft.size
          Tuple.fromArray((0 until tplSize).map(i => expr(())(() => '{ data(${ Expr(i) }) })).toArray).asInstanceOf[Tuple.Map[Args,Computes]]
        })) 
      }
    }
  }

  inline def ref[T](body : (given QuoteContext)=>Computes[T]) : Computes[T] =
    Ref(body, (given QuoteContext)=>summonFrom {
      case tp : Type[T] => tp
    })

  def let[V:Type,T:Type](value : Computes[V], body : Computes[V]=>Computes[T]) = {
    val name = Name[V]()
    NameBinding(name, value, body(name))
  }

  def expr[Args <: Tuple, Result : Type, F]
          (args : Args)(fn : F)
          (given tpl : TupledFunction[F,Tuple.Map[Tuple.InverseMap[Args,Computes],Expr]=>Expr[Result]])
          (given Tuple.IsMappedBy[Computes][Args]): Computes[Result] = {
    type PlainArgs = Tuple.InverseMap[Args,Computes]
    type ExprArgs = Tuple.Map[PlainArgs,Expr]
    Code(
      listArgs =>
        tpl.tupled(fn)(Tuple.fromArray(listArgs.toArray).asInstanceOf[ExprArgs]),
      args.toArray.toList.asInstanceOf[List[Computes[_]]])
  }

  inline def makeFunctionArgs[Args <: Tuple] <: Tuple = inline erasedValue[Args] match {
    case _ : Unit => ()
    case _ : (hd *: tl) => {
      type H = hd
      summonFrom {
        case given _ : Type[H] =>
          Name[H]() *: makeFunctionArgs[tl]
      }
    }
  }

  inline def fun[Args <: Tuple : Type, Result : Type, F]
                (fn : F)
                (given tpl : TupledFunction[F,Args=>Computes[Result]])
                (given Tuple.IsMappedBy[Computes][Args], QuoteContext)
  : Computes[Tuple.InverseMap[Args,Computes]==>Result] = {
    type PlainArgs = Tuple.InverseMap[Args,Computes]
    val args : Args = makeFunctionArgs[PlainArgs].asInstanceOf[Args]
    Function(tpl.tupled(fn)(args), args.toArray.toList.asInstanceOf[List[Name[_]]])
  }

  /*
  import scala.language.implicitConversions

  inline given ComputesFromFunction[F, Args <: Tuple, Result]:
                                   Conversion[F,(given TupledFunction[F,Args=>Computes[Result]], Tuple.IsMappedBy[Computes][Args])=>Computes[Tuple.InverseMap[Args,Computes]==>Result]] = new {
    def apply(f : F) = fun(f)
  }*/

  def (c : Computes[Args==>Result]) apply[Args <: Tuple, Result : Type](args : Tuple.Map[Args,Computes]) : Computes[Result] =
    Application(c, args.toArray.toList.asInstanceOf[List[Computes[_]]])

  def (c : Computes[Boolean]) branch[Result : Type](t : Computes[Result], f : Computes[Result]) : Computes[Result] =
    Branch(c, t, f)

  def const[T : Type : Liftable](t : T) : Computes[T] =
    Constant(t)

  given ComputesFromConstant[T : Type : Liftable] : Conversion[T,Computes[T]] {
    def apply(t : T) = const(t)
  }

  final case class Composite[T : Type, R <: Rule.Instance[T]](
    val rule : R,
    val rewrite : Rule.RewriteContext=>Rule.CRewrite[T],
    val lower : Rule.RewriteContext=>Rule.CRewrite[T],
    val members : List[Computes[_]],
    val handles : List[CHandle[_]]) extends Computes[T]
  {
    val theType = summon[Type[T]]
  }
  
  final case class Code[Result : Type](val fn : List[Expr[_]]=>Expr[Result], val args : List[Computes[_]]) extends Computes[Result] {
    val theType = summon[Type[Result]]
  }

  final case class Application[Args <: Tuple, Result : Type](val fn : Computes[Args==>Result], val args : List[Computes[_]]) extends Computes[Result] {
    val theType = summon[Type[Result]]
  }

  final case class Function[Args <: Tuple : Type, Result : Type](
    val body : Computes[Result],
    val args : List[Name[_]])(given QuoteContext) extends Computes[Args==>Result]
  {
    val theType = summon[Type[Args==>Result]]
  }

  final case class NameBinding[V, T : Type](val name : Name[V], val value : Computes[V], val body : Computes[T]) extends Computes[T] {
    val theType = summon[Type[T]]
  }

  final case class Constant[T : Type : Liftable](val v : T) extends Computes[T] {
    val theType = summon[Type[T]]
    val liftable = summon[Liftable[T]]
  }

  final case class Branch[T : Type](val condition : Computes[Boolean], val t : Computes[T], val f : Computes[T]) extends Computes[T] {
    val theType = summon[Type[T]]
  }

  final case class DispatchTable[Argument : Type : Liftable, Result : Type](
    val input : Computes[Argument],
    val pairs : List[(Argument,Computes[Result])],
    val default : Option[Computes[Result]]) extends Computes[Result]
  {
    val theType = summon[Type[Result]]
    val argType = summon[Type[Argument]]
    val argLiftable = summon[Liftable[Argument]]
  }

  final class Name[T : Type] extends Computes[T] {
    val theType = summon[Type[T]]
  }

  final class Ref[T](val ref : (given QuoteContext)=>Computes[T], val getType : (given QuoteContext)=>Type[T]) extends Computes[T] {
    val theType = null
  }

}

sealed abstract class Rule {

  protected inline def rule[Handles <: Tuple, F, T : Type]
                           (body : F)
                           (given tpl : TupledFunction[F,Handles=>Rule.R[T]])
                           (given Tuple.IsMappedBy[CHandle][Handles]) <: Rule.Instance[T] = {
    val thisRule = this
    new Rule.Instance[T] {
      val rule = thisRule
      type CHandles = Handles
      type Members = Tuple.InverseMap[Handles,CHandle]
      type ComputesMembers = Tuple.Map[Members,Computes]
      def apply(members : ComputesMembers) : Computes[T] = {
        lazy val handles : Handles = Rule.makeHandles[0,Handles](result)
        lazy val ruleR : Rule.R[T] = tpl.tupled(body)(handles)
        lazy val result : Computes[T] = Computes.Composite(
          this,
          ctx => ruleR.rewrite(given ctx),
          ctx => ruleR.lower(given ctx),
          members.toArray.toList.asInstanceOf[List[Computes[_]]],
          handles.toArray.toList.asInstanceOf[List[CHandle[_]]])
        result
      }
      def matchRewrite(fn : Handles=>Rule.CRewrite[T]) : Rule.CRewrite[T] =
        Rule.MatchRewrite(thisRule, fn)
    }
  }
}

object Rule {

  sealed abstract class RewriteContext {
    // TODO
  }

  sealed abstract class CRewrite[T] {
    // TODO
  }

  final case class MatchRewrite[T, R <: Rule, Handles <: Tuple](val rule : R, val fn : Handles=>CRewrite[T]) extends CRewrite[T]

  sealed abstract class Instance[T] {
    val rule : Rule
    type CHandles <: Tuple
    type Members <: Tuple
    type ComputesMembers <: Tuple
    def apply(members : ComputesMembers) : Computes[T]
    def matchRewrite(fn : CHandles=>CRewrite[T]) : CRewrite[T]
  }
  
  abstract class R[T] {
    def rewrite : (given RewriteContext)=>CRewrite[T]
    def lower : (given RewriteContext)=>CRewrite[T]
  }

  private[towers] inline def makeHandles[Index <: Int, Members <: Tuple](ownerRef : =>Computes[_]) : Members = inline erasedValue[Members] match {
    case _ : Unit => ().asInstanceOf[Members]
    case _ : (CHandle[hd] *: tl) => (new CHandle[hd] {
      val index = constValue[Index]
      lazy val owner = ownerRef
    } *: makeHandles[S[Index], tl](ownerRef)).asInstanceOf[Members]
  }
}

// test

object TupleConcat extends Rule {
  def apply[L <: Tuple : Type, R <: Tuple : Type](given QuoteContext) = rule {
    (lhs : CHandle[L], rhs : CHandle[R]) => new Rule.R[Tuple.Concat[L,R]] {
      def rewrite = ???
      def lower = ???
    }
  }
}

