package polyparse.computes

import scala.collection.mutable.{HashMap, HashSet}

import quoted._

class ComputesKey()

sealed abstract class Computes[Tp : Type](implicit val key : ComputesKey) {
  type T = Tp
  val tType = implicitly[Type[T]]
}

sealed abstract class RuntimeInstruction[+T]
type FunctionType[-Arg,+Result] = Arg => RuntimeInstruction[Result]

case class ReturnInstruction[+T](val value : T) extends RuntimeInstruction[T]
case class PushInstruction[+T,Arg,Result]
                          (val push : FunctionType[Arg,Result], val tail : RuntimeInstruction[T])
                          extends RuntimeInstruction[T]

object Computes {

  type C = Computes

  implicit def DefaultComputesKey : ComputesKey = ComputesKey()

  def unapply[T](c : Computes[T]) : Option[Computable[T]] = c match {
    case op : ComputesOpaque[T] => Some(op.computable)
    case _ => None
  }

  def const[T : Type : Liftable](value : T) : Computes[T] = ComputesConst(value)
  def function[Arg : Type, Result : Type](fn : Computes[Arg] => Computes[Result]) : Computes[FunctionType[Arg,Result]] = {
    val v = new ComputesAbstract[Arg]{}
    ComputesFunction(v, fn(v))
  }

  implicit class ComputesConst[T : Type : Liftable]
                              (val value : T)
                              (implicit key : ComputesKey)
                              extends Computes[T]()(implicitly[Type[T]], key) {
    val liftable = implicitly[Liftable[T]]
  }

  implicit class ComputesApplicableOps[Arg, Result : Type](fn : Computes[FunctionType[Arg,Result]]) {
    def apply(arg : Computes[Arg]) : Computes[Result] =
      ComputesApply(fn, arg)(arg.tType, implicitly[Type[Result]], implicitly[ComputesKey])
  }

  implicit class ComputesOps[T : Type](c : Computes[T]) {
    def let[Result : Type](fn : Computes[T] => Computes[Result]) : Computes[Result] = 
      function(fn).apply(c)
  }

  def expandOpaques[T](c : Computes[T], visited : HashSet[ComputesKey], indirects : HashMap[ComputesKey, Computes[_]]) : Computes[T] =
    if visited(c.key) then
      indirects(c.key).asInstanceOf[Computes[T]]
    else {
      visited += c.key
      implicit val e1 = c.tType
      val result : Computes[T] = c match {
        case _ : ComputesConst[T] => c
        case _ : ComputesAbstract[T] => c
        case ComputesMap(from, fn) => {
          implicit val e2 = from.tType
          val from2 = expandOpaques(from, visited, indirects)
          ComputesMap(from2, fn)
        }
        case ComputesFunction(arg, body) => {
          implicit val e2 = arg.tType
          implicit val e3 = body.tType
          val body2 = expandOpaques(body, visited, indirects)
          ComputesFunction(arg, body2)
        }
        case ComputesApply(fn, arg) => {
          implicit val e2 = arg.tType
          val fn2 = expandOpaques(fn, visited, indirects)
          val arg2 = expandOpaques(arg, visited, indirects)
          ComputesApply(fn2, arg2)
        }
        case ComputesSwitch(arg, cases, default) => {
          implicit val e2 = arg.tType
          val arg2 = expandOpaques(arg, visited, indirects)
          val cases2 = cases.map(expandOpaques(_, visited, indirects))
          val default2 = default.map(expandOpaques(_, visited, indirects))
          ComputesSwitch(arg2, cases2, default2)
        }
        case ind : ComputesIndirect[T] => {
          ComputesIndirect(expandOpaques(ind.computes, visited, indirects))
        }
        case op : ComputesOpaque[T] => {
          val comp = op.computable.toComputes
          expandOpaques(comp, visited, indirects)
        }
      }
      indirects += ((c.key, result))
      result
    }

  def getComputesBlocks[T](c : Computes[T], visited : HashSet[ComputesKey]) : List[Computes[_]] =
    if visited(c.key) then
      List.empty
    else {
      visited += c.key
      c match {
        case _ : ComputesConst[T] => List.empty
        case _ : ComputesAbstract[T] => List.empty
        case ComputesMap(from, _) => getComputesBlocks(from, visited)
        case ComputesFunction(_, body) =>
          List(body) ++ getComputesBlocks(body, visited)
        case ComputesApply(fn, arg) =>
          getComputesBlocks(arg, visited) ++ getComputesBlocks(fn, visited)
        case ComputesSwitch(arg, cases, default) => 
          getComputesBlocks(arg, visited) ++
          cases.flatMap(getComputesBlocks(_, visited)) ++
          default.map(getComputesBlocks(_, visited)).getOrElse(List.empty)
        case ind : ComputesIndirect[T] =>
          List(ind) ++ getComputesBlocks(ind.computes, visited)
        case op : ComputesOpaque[T] => ??? // opaques should be removed before getting blocks
      }
    }

  def compileImpl[Arg,Result](c : Computes[FunctionType[Arg,Result]]) : Expr[Arg=>Result] = {

    val flattened = expandOpaques(c, HashSet(), HashMap())
    val blocks = getComputesBlocks(flattened, HashSet())

    // TODO: pass to minimise indirects
    ???
    
  }

  implicit class ComputesFunctionCompiler[Arg,Result]
                                         (self : Computes[FunctionType[Arg,Result]]) {
    def compile : Expr[Arg=>Result] = compileImpl(self)
  }

  implicit class ComputesValueCompiler[T, A, R]
                                      (self : Computes[T])
                                      (implicit ev : implicits.Not[T <:< FunctionType[A,R]]) {
    def compile : Expr[T] = {
      implicit val e1 = self.tType
      function[Unit,T](u => self).compile.apply('{()})
    }
  }

  implicit class ComputesOpaque[T : Type]
                               (val computable : Computable[T])
                               (implicit key : ComputesKey)
                               extends Computes[T]()(implicitly[Type[T]], key)

  implicit class ComputesPair[Left : Type, Right : Type]
                                  (val pair: (Computes[Left], Computes[Right]))
                                  (implicit key : ComputesKey)
                                  extends Computes[(Left,Right)]()(implicitly[Type[(Left,Right)]], key)
}

import Computes._

trait Computable[T] {
  def toComputes : Computes[T]
  def tryReduce : Option[Computes[T]]
}

sealed abstract class ComputesAbstract[T : Type]
                                      (implicit key : ComputesKey)
                                      extends Computes[T]()(implicitly[Type[T]], key)

case class ComputesMap[From : Type, To : Type]
                      (from : Computes[From], fn : Expr[From=>To])
                      (implicit key : ComputesKey)
                      extends Computes[To]()(implicitly[Type[To]], key)

case class ComputesFunction[Arg : Type, Result : Type]
                           (arg : ComputesAbstract[Arg], body : Computes[Result])
                           (implicit key : ComputesKey)
                           extends Computes[FunctionType[Arg,Result]]()(implicitly[Type[FunctionType[Arg,Result]]], key)

case class ComputesApply[Arg : Type, Result : Type]
                        (fn : Computes[FunctionType[Arg,Result]], arg : Computes[Arg])
                        (implicit key : ComputesKey)
                        extends Computes[Result]()(implicitly[Type[Result]], key)

case class ComputesSwitch[Arg : Type, Result : Type]
                         (arg : Computes[Arg], cases : List[Computes[Result]], default : Option[Computes[Result]])
                         (implicit key : ComputesKey)
                         extends Computes[Result]()(implicitly[Type[Result]], key)

class ComputesIndirect[T : Type]
                      (c : =>Computes[T])
                      (implicit key : ComputesKey)
                      extends Computes[T]()(implicitly[Type[T]], key) {
  lazy val computes = c
}

