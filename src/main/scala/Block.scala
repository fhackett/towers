package polyparse.block

import quoted._

/*type BlockReference[In, Out] = (Int,Tuple)

sealed abstract class Value[Tp : Type] {
  type T = Tp
  val tType = implicitly[Type[T]]

  def map[T2 : Type](fn : Expr[Tp=>T2]) : Value[T2] = MapValue(this, fn)
  def ::[T2 : Type](v : Value[T2]) : Value[(Tp,T2)] = MakeTupleValue(this, v)
}

abstract class RootValue[T : Type] extends Value[T]

case class MapValue[From : Type, To : Type]
                   (val from : Value[From], val fn : Expr[From=>To])
                   extends Value[To]

case class MakeTupleValue[Left : Type, Right : Type]
                         (val left : Value[Left], val right : Value[Right])
                         extends Value[(Left,Right)]

case class ConstValue[T : Type : Liftable](val v : T) extends Value[T] {
  val liftable = implicitly[Liftable[T]]
}

sealed abstract class Block[I : Type, O : Type] {
  type Out = O
  type In = I
  val tIn = implicitly[Type[In]]
  val tOut = implicitly[Type[Out]]

  type Key = AnyRef
  val key = new Key{}

  def flatMap[Out2 : Type](fn : Value[Out] => Block[Unit,Out2]) : Block[In,Out2] = {
    val nVal = new RootValue[Out]{}
    SequenceBlock(this, MakeValueBlock(nVal, fn(nVal)))
  }
  def map[Out2 : Type](fn : Value[Out] => Value[Out2]) : Block[In,Out2] = {
    val nVal = new RootValue[Out]{}
    SequenceBlock(this, MakeValueBlock(nVal, ConsumeValueBlock(fn(nVal))))
  }

  def compile : Expr[I => O] = {
    
    def containsIndirection[In,Out](block : Block[In,Out]) : Boolean = block match {
      case IdentityBlock() => false
      case OpaqueBlock(_) => false
      case MatchTupleBlock(_,next) => containsIndirection(next)
      case MakeValueBlock(_,next) => containsIndirection(next)
      case SequenceBlock(first, secont) => containsIndirection(first) || containsIndirection(second)
      case SwitchBlock(cases, default) => cases.exists(containsIndirection) || containsIndirection(default)
      case ThunkBlock(body) => false
      case ApplyBlock() => true
      case _ : LazyBlock[In,Out] => true
    }

    def getBlockSequence[In, Out](block : Block[In,Out], visited : Set[Key]) : (List[Block[_,_]], Set[Key]) =
      if visited(block.key)
        (List(), visited)
      else
        block match {
          case IdentityBlock() => (List.empty, visited & block.key)
          case OpaqueBlock(_) => (List.empty, visited & block.key)
          case MatchTupleBlock(_,next) => getBlockSequence(next, visited & block.key)
          case MakeValueBlock(_,next) => getBlockSequence(next, visited & block.key)
          case SequenceBlock(first, second) => {
            val (l1, v1) = getBlockSequence(first, visited & block.key & first.key)
            val (l2, v2) = getBlockSequence(second, v1 & second.key)
            if containsIndirection(first) // if first indirects, we need a new block for second
              (l1 ++ List(second) ++ l2, v2)
            else
              (l1 ++ l2, v2)
          }
          case SwitchBlock(cases, default) => {
            val (l1, v1) = cases.foldLeft((List.empty, visited & block.key))((acc, cas) => {
              val (l, v) = getBlockSequence(cas._2, acc._2)
              (acc._1 ++ l, v)
            })
            val (l2, v2) = getBlockSequence(default, v1)
            (l1 ++ l2, v2)
          }
          case ThunkBlock(body) => {
            val (l, v) = getBlockSequence(body, visited & block.key)
            (List(body) ++ l, v) // thunked block gets a PC
          }
          case ApplyBlock() => (List.empty, visited & block.key)
          case b : LazyBlock[In,Out] => getBlockSequence(b.block, visited & block.key)
        }

    val (blockSequence, _) = getBlockSequence(this, Set.empty)
    val pcMap = blockSequence.map(_.key).zipWithIndex.toMap

    def valueCodegen[T : Type](value : Value[T], vars : (v : RootValue[_]) => Expr[v.T]) : Expr[T] = value match {
      case v : RootValue[T] => vars(v)
      case MapValue(v, fn) => fn(valueCodegen(v, vars))
      case MakeTupleValue(v1, v2) => '{ ( ${ valueCodegen(v1, vars) }, ${ valueCodegen(v2, vars) } ) }
      case ConstValue(v) => v.toExpr(v.liftable)
    }

    def inlineCodegen[In : Type, Out : Type]
                     (block : Block[In,Out], vars : (v : RootValue[_]) => Expr[v.T])
                     : Expr[In=>Out] = block match {
      case IdentityBlock() => '{ x => x }
      case OpaqueBlock(fn) => fn
      case MatchTupleBlock(left, right, next) => '{ x => x match {
        case (l, r) => ${
          inlineCodegen(next, v =>
            if (v == left)
              '{l}
            else if (v == right)
              '{r}
            else vars(v))
        }
      } }
      case MakeValueBlock(root, next) => '{ x => { val v = x; ${ inlineCodegen(next, va =>
        if (va == root)
          '{v}
        else
          vars(va))
      } } }
      case SequenceBlock(first, second) => '{ x => ${ inlineCodegen(second, vars)(inlineCodegen(first, vars)('{x})) } }
      case SwitchBlock(cases, default) => ???
      case ThunkBlock(body) => '{ ( ${ pcMap(body.key).toExpr }, ??? ) } // TODO: gather and tuple-ify closure
      case ApplyBlock | LazyBlock => ??? // unreachable, inline gen only here
    }

    def codegen[In : Type, Out : Type]
               (block : Block[In,Out], vars : (v : RootValue[_]) => Expr[v.T])
               (implicit reflection : Reflection)
               : Expr[In=>(List[(Int,Tuple)],Out)] = block match {
      case IdentityBlock() => '{ x => (List.empty,x) }
      case OpaqueBlock(fn) => '{ x => (List.empty,fn(x)) }
      case MatchTupleBlock(left, right, next) => '{ x => x match {
        case (l, r) => ${
          codegen(next, v =>
            if (v == left)
              '{l}
            else if (v == right)
              '{r}
            else vars(v))
        }
      } }
      case MakeValueBlock(root, next) => '{ x => { val v = x; ${ codegen(next, va =>
        if (va == root)
          '{v}
        else
          vars(va))
      } } }
      case SequenceBlock(first, second) =>
        if containsIndirection(first)
          '{ x => {
            val (npc,result) = ${ codegen(first, vars)('{x}) }
            ( ${ pcMap(second.key).toExpr }, ??? ) // TODO: gather and tuple-ify closure
          } } 
        else
          '{ x => ${ codegen(second, vars)(inlineCodegen(first, vars)('{x})) } }
      case SwitchBlock(cases, default) => ??? // TODO: implement (same for inline)
      case b : LazyBlock[In,Out] => '{ ( (${pcMap(b.block.key).toExpr},()) :: List.empty, null ) }
    }

  }
}

// grammar[T,ET] => BlockReference[ET,(_,grammar[T,ET])]

case class IdentityBlock[T : Type]() extends Block[T,T]

case class OpaqueBlock[In : Type, Out : Type]
                      (val expr : Expr[In=>Out])
                      extends Block[In,Out] {
}

case class MatchTupleBlock[Left : Type, Right : Type, Out : Type]
                          (val left : RootValue[Left], val right : RootValue[Right], val block : Block[Unit,Out])
                          extends Block[(Left,Right),Out]

case class MakeValueBlock[In : Type, Out : Type]
                         (val v : RootValue[In], val block : Block[Unit,Out])
                         extends Block[In,Out]

case class SequenceBlock[In : Type, Mid : Type, Out : Type]
                     (val first : Block[In,Mid], val second : Block[Mid,Out])
                     extends Block[In,Out]

case class SwitchBlock[In : Type, Out : Type]
                      (val cases : Seq[(Value[In],Block[Unit,Out])], val default : Block[In,Out])
                      extends Block[In,Out]

case class ThunkBlock[In : Type, Out : Type]
                     (val body : Block[In,Out])
                     extends Block[Unit,BlockReference[In,Out]]

case class ApplyBlock[Args : Type, Out : Type]()
                     extends Block[(Args, BlockReference[Args,Out]), Out]

class LazyBlock[In : Type, Out : Type]
               (block_ : => Block[In,Out])
               extends Block[In,Out] {
  lazy val block = block_
}
*/

// flatMap
// filter ends parse path (assuming we can get return type to work)
// map goes from var to var (in order to match flatMap type)
// switch coalescing (requires knowledge of original Grammar ... or a specific form, nested match expressions)
// left-recursion support? (requires knowledge of original Grammar)
// generally: Block can provide source AST as an attribute, enabling analysis and opt. despite mixing AST types
// implement variable instantiations, manipulating stack as necessary. replaces keepArg
// implement variable closures for block lambdas
// implement constant folding (important for inlining trivially inline-able block lambdas)
// allow Grammar to contain Blocks, impure like Parsec but (hopefully) optimisable
// - source attributes may be hidden / nested, optimiser might have to look carefully
// allow implicit conversions from Grammar to Block (but keeping the source attribute)
// generate match expressions over pc using TASTy
// idea: push-style streams, grammar is param for tokeniser / sequence traverser. allows nested / piped parsers
// - last one is pull-style
// - iteration protocol: at Block level, have special returns that allow yielding. support iterator composition
// - iteration protocol: at Block level, also stream (non-suppressed) errors as they happen
// - iteration protocol: pause and resume also done at Block level, Block only needs to understand arg, return and closures
// idea 2: relational searches, requires relational database storage. take as argument and use via closure?
// idea 3: stream combinators, maybe useful for tokenisers. capable of nesting with the rest
// idea 4: regex combinators, optimised regex support. subset of grammars, useful for when you know there is one result
// problem: streaming parsers vs. backtracking parsers vs. n-lookahead parsers; how to enforce the difference?
// - streaming and n-lookahead are indistinguishable
// - backtracking and streaming should be different - should be able to provide a one-way iterator to a streaming but not
//   backtracking parser
// - backtracking needs mark-restore support, part of the iterator protocol?
//
// parser protocol:
// - single-item alternatives passed as continuations, discarded after one element is consumed
// - actual backtracking also passed (around) as continuations
// - use closures for anything "interesting"
// - left-recursion accounted for by ???; needs ahead of time grammar support

/*object API {

  def const[T : Type : Liftable](v : T) : Block[Unit,T] = ConsumeValueBlock(ConstValue(v))

  implicit class ConsumeValueBlock[T : Type](val v : Value[T]) extends Block[Unit,T]
  implicit class ExprValue[T : Type](e : Expr[T]) extends Value[T]
}*/

sealed abstract class Computes[Tp : Type] {
  type T = Tp
  val tType = implicitly[Type[T]]

  type Key = AnyRef
  val key = new Key{}
}

object Computes {

  def const[T : Type : Liftable](value : T) : Computes[T] = ComputesConst(value)
  def function[Arg : Type, Result : Type](fn : Computes[Arg] => Computes[Result]) : Computes[Arg=>Result] = {
    val v = new ComputesAbstract[Arg]{}
    ComputesFunction(v, fn(v))
  }

  trait IsAFunction[T]

  implicit def IsAFunctionEvidence[A,B] : IsAFunction[A=>B] = null.asInstanceOf[IsAFunction[A=>B]]

  implicit class ComputesConst[T : Type : Liftable]
                              (val value : T)
                              (implicit ev : implicits.Not[IsAFunction[T]])
                              extends Computes[T] {
    val liftable = implicitly[Liftable[T]]
  }

  implicit class ComputesApplicableOps[Arg, Result : Type](fn : Computes[Arg=>Result]) {
    def apply(arg : Computes[Arg]) : Computes[Result] = ComputesApply(fn, arg)(arg.tType, implicitly[Type[Result]])
  }

  implicit class ComputesOps[T : Type](c : Computes[T]) {
    def let[Result : Type](fn : Computes[T] => Computes[Result]) : Computes[Result] = 
      function(fn).apply(c)
  }
}

sealed abstract class ComputesAbstract[T : Type] extends Computes[T]

case class ComputesMap[From : Type, To : Type](from : Computes[From], fn : Expr[From=>To]) extends Computes[To]

case class ComputesFunction[Arg : Type, Result : Type]
                           (arg : ComputesAbstract[Arg], body : Computes[Result])
                           extends Computes[Arg=>Result]

case class ComputesApply[Arg : Type, Result : Type]
                        (fn : Computes[Arg=>Result], arg : Computes[Arg])
                        extends Computes[Result]

case class ComputesSwitch[Arg : Type, Result : Type]
                         (arg : Computes[Arg], cases : List[Computes[Result]], default : Option[Computes[Result]])
                         extends Computes[Result]

class ComputesIndirect[T : Type](c : =>Computes[T]) extends Computes[T] {
  lazy val computes = c
}

