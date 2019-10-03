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

sealed abstract class ComputesKey
case object NoKey extends ComputesKey
final case class ComputesKeyI(val i : Int) extends ComputesKey

trait KeyContext {
  def getKeyOf(obj : AnyRef) : ComputesKey
}

class ==>[Args <: Tuple, Result](val pc : Int, val closure : Array[Any])

sealed abstract class CHandle[T] {
  val index : Int
  lazy val owner : Computes[_]
}

sealed abstract class Computes[T] {
  def key(given keyCtx : KeyContext) : ComputesKey = keyCtx.getKeyOf(this)
}

object Computes {

  def compile[T : Type](c : Computes[T])(given qctx : QuoteContext) : Expr[T] =
    '{ ??? }

  trait ArgsFromTuple[Tpl <: Tuple] {
    val size : Int 
  }

  given ArgsFromTuple[Unit] {
    val size = 0
  }

  given [Hd, Tl <: Tuple](given aft : ArgsFromTuple[Tl]) : ArgsFromTuple[Hd *: Tl] {
    val size = aft.size + 1
  }

  def compileFn[Args <: Tuple : Type, Result : Type]
               (c : Computes[Args==>Result])
               (given qctx : QuoteContext, aft : ArgsFromTuple[Args]) : Expr[Args=>Result] = '{
    (args : Args) => {
      val data = args.toIArray
      ${
        compile(c({
          val tplSize = aft.size
          Tuple.fromArray((0 until tplSize).map(i => expr((), () => '{ data(${ Expr(i) }) })).toArray).asInstanceOf[Tuple.Map[Args,Computes]]
        })) 
      }
    }
  }

  def ref[T](body : (given QuoteContext)=>Computes[T]) : Computes[T] = Ref(body)

  def let[V:Type,T](value : Computes[V], body : Computes[V]=>Computes[T]) = {
    val name = Name[V]()
    Binding(name, value, body(name))
  }

  def expr[Args <: Tuple, Result : Type, F]
          (args : Args, fn : F)
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

  inline def fun[Args <: Tuple, Result, F](fn : F)(given tpl : TupledFunction[F,Args=>Computes[Result]])(given Tuple.IsMappedBy[Computes][Args]) : Computes[Tuple.InverseMap[Args,Computes]==>Result] = {
    type PlainArgs = Tuple.InverseMap[Args,Computes]
    val args : Args = makeFunctionArgs[PlainArgs].asInstanceOf[Args]
    Function(tpl.tupled(fn)(args), args.toArray.toList.asInstanceOf[List[Name[_]]])
  }

  // broken by lampepfl/dotty#7349
  inline given ComputesFromFunction[Args <: Tuple, Result, F](given tpl : TupledFunction[F,Args=>Computes[Result]])(given Tuple.IsMappedBy[Computes][Args]): Conversion[F,Computes[Tuple.InverseMap[Args,Computes]==>Result]] = new {
    def apply(f : F) = fun(f)
  }

  def (c : Computes[Args==>Result]) apply[Args <: Tuple, Result](args : Tuple.Map[Args,Computes]) : Computes[Result] =
    Application(c, args.toArray.toList.asInstanceOf[List[Computes[_]]])

  def (c : Computes[Boolean]) branch[Result](t : Computes[Result], f : Computes[Result]) : Computes[Result] =
    Branch(c, t, f)

  def const[T : Type : Liftable](t : T) : Computes[T] =
    Constant(t)

  given ComputesFromConstant[T : Type : Liftable] : Conversion[T,Computes[T]] {
    def apply(t : T) = const(t)
  }

  final case class Composite[T : Type, R <: Rule.Instance[T]](val rule : R, val members : List[Computes[_]], val handles : List[CHandle[_]]) extends Computes[T] {
    val theType = summon[Type[T]]
  }
  
  final case class Code[Result : Type](val fn : List[Expr[_]]=>Expr[Result], val args : List[Computes[_]]) extends Computes[Result] {
    val theType = summon[Type[Result]]
  }

  final case class Application[Args <: Tuple, Result](val fn : Computes[Args==>Result], val args : List[Computes[_]]) extends Computes[Result]

  final case class Function[Args <: Tuple, Result](val body : Computes[Result], val args : List[Name[_]]) extends Computes[Args==>Result]

  final case class Binding[V, T](val name : Name[V], val value : Computes[V], val body : Computes[T]) extends Computes[T]

  final case class Constant[T : Type : Liftable](val v : T) extends Computes[T] {
    val theType = summon[Type[T]]
    val liftable = summon[Liftable[T]]
  }

  final case class Branch[T](val condition : Computes[Boolean], val t : Computes[T], val f : Computes[T]) extends Computes[T]

  final class Name[T : Type] extends Computes[T] {
    val theType = summon[Type[T]]
  }

  final class Ref[T](val ref : (given QuoteContext)=>Computes[T]) extends Computes[T]

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
          this, members.toArray.toList.asInstanceOf[List[Computes[_]]],
          handles.toArray.toList.asInstanceOf[List[CHandle[_]]])
        result
      }
      def matchRewrite(fn : Handles=>Rule.CRewrite[T]) : Rule.CRewrite[T] =
        Rule.MatchRewrite(thisRule, fn)
    }
  }
}

object Rule {

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
    def rewrite : Any//CRewrite[T]
    def lower : Any//CLower[T]
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

