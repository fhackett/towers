package towers.grammar

import quoted._

import towers.computes.{Computes,Computable}
import Computes._


type Error = String

class InputSource[E](pc : Int, closure : Array[Any]) extends ==>[((E,Int,InputSource[E])==>Unit,Int|=>Unit),Unit](pc, closure)

type ShallowFailFn = Error|=>Unit
type DeepFailFn = Error|=>Unit
type SuccessFn[E,T] = (T,InputSource[E])==>Unit
type Grammar[E,T] = (InputSource[E],SuccessFn[E,T],ShallowFailFn,DeepFailFn)==>Unit

object Grammar {
  def term[E : Type : Liftable](e : E) : Computes[Grammar[E,E]] = TermGrammar(const(e))
  def term[E : Type : Liftable, I <: Iterable[E] : Type : Liftable](it : I) : Computes[Grammar[E,I]] = {
    var lhs : Computes[Grammar[E,E]] = null
    for(e <- it) {
      if lhs != null then {
        lhs = lhs.flatMap(_ => term(e))
      } else {
        lhs = term(e)
      }
    }
    lhs.flatMap(_ => succeed(const(it)))
  }

  def succeed[E : Type, T : Type](t : Computes[T]) : Computes[Grammar[E,T]] =
    SuccessGrammar(t)

  def fail[E : Type, T : Type](err : Computes[Error]) : Computes[Grammar[E,T]] =
    FailGrammar(err)

  def choose[E : Type, T : Type](left : Computes[Grammar[E,T]], right : Computes[Grammar[E,T]]) : Computes[Grammar[E,T]] =
    DisjunctGrammar(left, right)

  implicit class GrammarOps[E : Type, T : Type](g : =>Computes[Grammar[E,T]]) {
    def flatMap[T2 : Type](fn : Computes[T] => Computes[Grammar[E,T2]]) : Computes[Grammar[E,T2]] =
      FlatMapGrammar(ref(g), fn)
    def map[T2 : Type](fn : Computes[T] => Computes[T2]) : Computes[Grammar[E,T2]] =
      g.flatMap((t : Computes[T]) => succeed(fn(t)))
    def filter(fn : Computes[T] => Computes[Boolean]) : Computes[Grammar[E,T]] =
      g.flatMap((t : Computes[T]) => fn(t).switch(List(const(true) -> succeed(t), const(false) -> fail(const("filter")))))

    def rep : Computes[Grammar[E,Seq[T]]] = {
      import scala.collection.mutable.ArrayBuffer

      lazy val rec : Computes[ArrayBuffer[T]|=>Grammar[E,Seq[T]]] =
        (buf : Computes[ArrayBuffer[T]]) =>
          choose(
            ref(g).flatMap(t => rec(expr((buf, t), {
              case (buf, t) => '{ ${ buf } += ${ t }; ${ buf } }
            }))),
          succeed(expr(buf, buf => '{ ${ buf }.toSeq })))
      rec(expr((), _ => '{ ArrayBuffer() }))
    }
  }

  implicit class IndexedSeqOps[E : Type, S <: IndexedSeq[E] : Type](seq : Computes[S]) {
    def length : Computes[Int] =
      expr(seq, seq => '{ ${ seq }.length })
    def apply(i : Computes[Int]) : Computes[E] =
      expr((seq, i), {
        case (seq, i) => '{ ${ seq }.apply(${ i }) }
      })
  }

  def makeIndexedSeqInput[E : Type, S <: IndexedSeq[E] : Type] : Computes[S|=>InputSource[E]] =
    (input : Computes[S]) => {
      lazy val rec : Computes[Int|=>InputSource[E]] =
        (i : Computes[Int]) =>
          ((onE : Computes[(E,Int,InputSource[E])==>Unit], onEOF : Computes[Int|=>Unit]) =>
            input.length.switch(
              List(i -> onEOF(i)),
              default=onE(input(i), i, rec(i+const(1))))) : Computes[InputSource[E]]
      rec(const(0))
    }

}

import Grammar._

abstract class GrammarComputable[E : Type, T : Type] extends Computable[Grammar[E,T]] {

}

class TermGrammar[E : Type](var term : Computes[E]) extends GrammarComputable[E,E] {
  def computesArity = 1
  def getComputesElement(n : Int) = n match {
    case 0 => term
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  def setComputesElement(n : Int, v : Computes[_]) = n match {
    case 0 => term = v.asInstanceOf[Computes[E]]
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  override def shallowClone = TermGrammar(term)

  def tryFold = None
  def flatten =
    (input : Computes[InputSource[E]], success : Computes[SuccessFn[E,E]], shallowFail : Computes[ShallowFailFn], deepFail : Computes[DeepFailFn]) =>
      input(
        ((e : Computes[E], i : Computes[Int], next : Computes[InputSource[E]]) =>
          e.switch(
            List(term -> success(e, next)),
            default=shallowFail(const("error")))) : Computes[(E,Int,InputSource[E])==>Unit],
        ((i : Computes[Int]) =>
          shallowFail(const("eof"))) : Computes[Int|=>Unit])
}

class SuccessGrammar[E : Type, T : Type](var t : Computes[T]) extends GrammarComputable[E,T] {
  def computesArity = 1
  def getComputesElement(n : Int) = n match {
    case 0 => t
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  def setComputesElement(n : Int, v : Computes[_]) = n match {
    case 0 => t = v.asInstanceOf[Computes[T]]
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  override def shallowClone = SuccessGrammar(t)
  
  def tryFold = None
  def flatten =
    (input : Computes[InputSource[E]], success : Computes[SuccessFn[E,T]], shallowFail : Computes[ShallowFailFn], deepFail : Computes[DeepFailFn]) =>
      success(t, input)
}

class FailGrammar[E : Type, T : Type](var err : Computes[Error]) extends GrammarComputable[E,T] {
  def computesArity = 1
  def getComputesElement(n : Int) = n match {
    case 0 => err
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  def setComputesElement(n : Int, v : Computes[_]) = n match {
    case 0 => err = v.asInstanceOf[Computes[Error]]
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  override def shallowClone = FailGrammar(err)
  
  def tryFold = None
  def flatten =
    (input : Computes[InputSource[E]], success : Computes[SuccessFn[E,T]], shallowFail : Computes[ShallowFailFn], deepFail : Computes[DeepFailFn]) =>
      shallowFail(err)
}

class FlatMapGrammar[E : Type, T1 : Type, T2 : Type](var g : Computes[Grammar[E,T1]], var fn : Computes[T1|=>Grammar[E,T2]]) extends GrammarComputable[E,T2] {
  def computesArity = 2
  def getComputesElement(n : Int) = n match {
    case 0 => g
    case 1 => fn
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  def setComputesElement(n : Int, v : Computes[_]) = n match {
    case 0 => g = v.asInstanceOf[Computes[Grammar[E,T1]]]
    case 1 => fn = v.asInstanceOf[Computes[T1|=>Grammar[E,T2]]]
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  override def shallowClone = FlatMapGrammar(g, fn)

  def tryFold = None
  def flatten =
    (input : Computes[InputSource[E]], success : Computes[SuccessFn[E,T2]], shallowFail : Computes[ShallowFailFn], deepFail : Computes[DeepFailFn]) =>
      g(
        input,
        (t1 : Computes[T1], next : Computes[InputSource[E]]) =>
          fn(t1).apply(next, success, deepFail, deepFail),
        shallowFail,
        deepFail)
}

class DisjunctGrammar[E : Type, T : Type](var left : Computes[Grammar[E,T]], var right : Computes[Grammar[E,T]]) extends GrammarComputable[E,T] {
  def computesArity = 2
  def getComputesElement(n : Int) = n match {
    case 0 => left
    case 1 => right
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  def setComputesElement(n : Int, v : Computes[_]) = n match {
    case 0 => left = v.asInstanceOf[Computes[Grammar[E,T]]]
    case 1 => right = v.asInstanceOf[Computes[Grammar[E,T]]]
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  override def shallowClone = DisjunctGrammar(left, right)
  
  def tryFold = None
  def flatten =
    (input : Computes[InputSource[E]], success : Computes[SuccessFn[E,T]], shallowFail : Computes[ShallowFailFn], deepFail : Computes[DeepFailFn]) =>
      left(
        input,
        success,
        (error : Computes[Error]) =>
          right(input, success, shallowFail, deepFail),
        deepFail)
}

class TryGrammar[E : Type, T : Type](var g : Computes[Grammar[E,T]]) extends GrammarComputable[E,T] {
  def computesArity = 1
  def getComputesElement(n : Int) = n match {
    case 0 => g
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  def setComputesElement(n : Int, v : Computes[_]) = n match {
    case 0 => g = v.asInstanceOf[Computes[Grammar[E,T]]]
    case _ => throw IndexOutOfBoundsException(n.toString)
  }
  override def shallowClone = TryGrammar(g)
  
  def tryFold = None
  def flatten =
    (input : Computes[InputSource[E]], success : Computes[SuccessFn[E,T]], shallowFail : Computes[ShallowFailFn], deepFail : Computes[DeepFailFn]) =>
      g(input, success, shallowFail, shallowFail)
}

