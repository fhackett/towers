package towers.computes

import Predef.{any2stringadd => _, _} // allow implicits to override +

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}
import scala.collection.{Seq}
import scala.collection.immutable.TreeSet

import quoted._
import tasty._

sealed abstract class ComputesKey
case object NoKey extends ComputesKey
final case class ComputesKeyI(val i : Int) extends ComputesKey

trait KeyContext {
  def getKeyOf(obj : AnyRef) : ComputesKey
}

sealed abstract class Rewrite[T]

final case class NoRewrite[T]() extends Rewrite[T]
final case class ResultRewrite[T](val result : Computes[T]) extends Rewrite[T]
final case class MatchRewrite[MatchMembers <: Tuple,MatchT,T,F](
  val handle : Computes[MatchT],
  val rulesToMatch : Rules[MatchMembers,MatchT],
  val next : F
) given TupledFunction[F,Tuple.Map[MatchMembers,[t]=>>ComputesHandle[t]]=>Rewrite[T]] extends Rewrite[T]
final case class ChooseRewrite[T](val first : Rewrite[T], val second : Rewrite[T]) extends Rewrite[T]

sealed trait RulesFns[Members <: Tuple,Result] {
  type ComputesMembers = Tuple.Map[Members,Computes]
  type RewriteFn
  type LowerFn
  val rewriteFnTupled : TupledFunction[RewriteFn,ComputesMembers=>given QuoteContext=>Rewrite[Result]]
  val lowerFnTupled : TupledFunction[LowerFn,ComputesMembers=>given QuoteContext=>Computes[Result]]
}

given [Members <: Tuple, Result, RewriteFn, LowerFn] as RulesFns[Members,Result]
  given (rewriteFnTupled : TupledFunction[RewriteFn,Tuple.Map[Members,Computes]=>given QuoteContext =>Rewrite[Result]])
  given (lowerFnTupled : TupledFunction[LowerFn,Tuple.Map[Members,Computes]=>given QuoteContext=>Computes[Result]])
{
  //type RewriteFn = RewriteFn_
  //type LowerFn = LowerFn_
  //val rewriteFnTupled = rewriteFnTupled_
  //val lowerFnTupled = lowerFnTupled_
}

abstract class Rules[Members <: Tuple, Result]
  given RulesFns[Members,Result]
{
  val rulesFns = the[RulesFns[Members,Result]]
  val rewrite : rulesFns.RewriteFn = rulesFns.rewriteFnTupled.untupled(_ => NoRewrite())
  val lower : rulesFns.LowerFn
}

sealed abstract class Computes[T] {
  def tType given QuoteContext : Type[T]
  def key given (keyCtx : KeyContext) : ComputesKey = keyCtx.getKeyOf(this)

  def compile given QuoteContext : Expr[T]
}

object Computes {
  def apply[Members <: Tuple, Result : Type](rules : Rules[Members,Result], members : rules.rulesFns.ComputesMembers) : Computes[Result] =
    ComputesComposite(rules, members)
}

final class ComputesName[T : Type] extends Computes[T] {
  def tType given QuoteContext = the[Type[T]]
}

final class DeferredComputes[T](val gen : given QuoteContext=>Computes[T]) extends Computes[T] {
  def tType given QuoteContext = ???
}

final class ComputesComposite[T : Type, Members <: Tuple](
  val rules : Rules[Members,T],
  val members : given QuoteContext=>rules.rulesFns.ComputesMembers)
  extends Computes[T]
{
  def tType given QuoteContext = the[Type[T]]
}

final class ComputesExpr[T : Type, Members <: Tuple, F](
  val mkExpr : F,
  val members : given QuoteContext=>Tuple.Map[Members,[t]=>>Computes[t]])
  given TupledFunction[F,(QuoteContext *: Tuple.Map[Members,[t]=>>Expr[t]])=>Expr[T]]
  extends Computes[T]
{
  def tType given QuoteContext = the[Type[T]]
}

final class ComputesHandle[T](val key : ComputesKey)

// test

/*object AddInts extends Rules[(Int,Int),Int] {
  val lower = (lhs : Computes[Int], rhs : Computes[Int]) => Computes(AddInts,(lhs, rhs))
}*/

