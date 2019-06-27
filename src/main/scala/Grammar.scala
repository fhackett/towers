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

class Cell[T](var t : T)

object Grammar {

  implicit def InputSourceInst[E : Type] : Computes.FnInst[InputSource[E]] = new {
    def apply(pc : Expr[Int], closure : Expr[Array[Any]]) = '{ InputSource(${ pc }, ${ closure }) }
  }

  def parse[E : Type, T : Type](g : Computes[Grammar[E,T]], input : Computes[InputSource[E]]) : Computes[Option[T]] =
    let(expr((), _ => '{ Cell[Option[T]](null) }), (cell : Computes[Cell[Option[T]]]) =>
        let(
          g(
            input,
            (t : Computes[T], _ : Computes[InputSource[E]]) => expr((cell, t), {
              case (cell, t) => '{ ${ cell }.t = Some(${ t }) }
            }),
            (_ : Computes[Error]) => expr(cell, cell => '{ ${ cell }.t = None }),
            (_ : Computes[Error]) => expr(cell, cell => '{ ${ cell }.t = None })),
          (unit : Computes[Unit]) =>
            expr((cell, unit), {
              case (cell, _) => '{ ${ cell }.t }
            })))

  def term[E : Type : Liftable](e : E) : Computes[Grammar[E,E]] = TermGrammar(const(e))
  def term[E : Type](e : Computes[E]) : Computes[Grammar[E,E]] = TermGrammar(e)

  def drop[E : Type, T : Type](g : Computes[Grammar[E,T]]) : Computes[Grammar[E,Unit]] =
    g.map((_ : Computes[T]) => const(()))

  def seq[E : Type : Liftable](first : E, rest : E*) : Computes[Grammar[E,Unit]] = {
    var lhs : Computes[Grammar[E,Unit]] = drop(term(const(first)))
    for(e <- rest) {
      lhs = lhs.flatMap((_ : Computes[Unit]) => drop(term(const(e))))
    }
    lhs
  }
  def seq[E : Type](first : Computes[E], rest : Computes[E]*) : Computes[Grammar[E,Unit]] = {
    var lhs : Computes[Grammar[E,Unit]] = drop(term(first))
    for(e <- rest) {
      lhs = lhs.flatMap((_ : Computes[Unit]) => drop(term(e)))
    }
    lhs
  }

  def str(str : String) : Computes[Grammar[Char,Unit]] =
    if str.length == 0 then {
      succeed(const(()))
    } else {
      seq(str.head, str.tail :_*)
    }

  def anyTerm[E : Type] : Computes[Grammar[E,E]] =
    AnyTermGrammar()

  def eofTerm[E : Type] : Computes[Grammar[E,Unit]] =
    EOFTermGrammar()

  def succeed[E : Type, T : Type](t : Computes[T]) : Computes[Grammar[E,T]] =
    SuccessGrammar(t)

  def fail[E : Type, T : Type](err : Computes[Error]) : Computes[Grammar[E,T]] =
    FailGrammar(err)

  def choose[E : Type, T : Type](c1 : Computes[Grammar[E,T]], c2 : Computes[Grammar[E,T]], cs : Computes[Grammar[E,T]]*) : Computes[Grammar[E,T]] =
    cs.foldLeft(DisjunctGrammar(c1,c2))((acc, c) => DisjunctGrammar(acc, c))

  def `try`[E : Type, T : Type](g : Computes[Grammar[E,T]]) : Computes[Grammar[E,T]] =
    TryGrammar(g)

  implicit class GrammarOps[E : Type, T : Type](g : =>Computes[Grammar[E,T]]) {
    def flatMap[T2 : Type](fn : Computes[T|=>Grammar[E,T2]]) : Computes[Grammar[E,T2]] =
      FlatMapGrammar(ref(g), fn)
    def map[T2 : Type](fn : Computes[T|=>T2]) : Computes[Grammar[E,T2]] =
      g.flatMap((t : Computes[T]) => succeed[E,T2](fn(t)))
    def filter(fn : Computes[T|=>Boolean]) : Computes[Grammar[E,T]] =
      g.flatMap((t : Computes[T]) => fn(t).switch(List(const(true) -> succeed[E,T](t), const(false) -> fail[E,T](const("filter")))))

    def rep(sep : Computes[Grammar[E,Unit]] = succeed(const(()))) : Computes[Grammar[E,Seq[T]]] = {
      import scala.collection.mutable.ArrayBuffer

      lazy val rec : Computes[ArrayBuffer[T]|=>Grammar[E,Seq[T]]] =
        (buf : Computes[ArrayBuffer[T]]) =>
          choose(
            sep.flatMap((_ : Computes[Unit]) =>
              ref(g).flatMap((t : Computes[T]) => ref(rec).apply(expr((buf, t), {
                case (buf, t) => '{ /*${ buf } += ${ t };*/ ${ buf } }
              })))),
            succeed(expr(buf, buf => '{ ${ buf }.toSeq })))

      choose(
        ref(g).flatMap((t : Computes[T]) =>
            ref(rec).apply(expr(t, t => '{
              val buf = ArrayBuffer[T]()
              //buf += ${ t }
              buf
            }))),
        succeed(expr((), _ => '{ Seq.empty })))
    }

    def repDrop(sep : Computes[Grammar[E,Unit]] = succeed(const(()))) : Computes[Grammar[E,Unit]] = {
      lazy val rec : Computes[Grammar[E,Unit]] =
        choose(
          sep.flatMap((_ : Computes[Unit]) => ref(g).flatMap((_ : Computes[T]) => ref(rec))),
          succeed(const(())))

      choose(
        ref(g).flatMap((_ : Computes[T]) => ref(rec)),
        succeed(const(())))
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

  def makeStringInput : Computes[String|=>InputSource[Char]] =
    (input : Computes[String]) => {
      lazy val rec : Computes[Int|=>InputSource[Char]] =
        (i : Computes[Int]) =>
          ((onE : Computes[(Char,Int,InputSource[Char])==>Unit], onEOF : Computes[Int|=>Unit]) =>
            expr(input, input => '{ ${ input }.length }).switch(
              List(i -> onEOF(i)),
              default=onE(
                expr((input, i), {
                  case (input, i) => '{ val v = ${ input }.charAt(${ i }); println(s"read $v"); v }
                }), i, rec(i+const(1))))) : Computes[InputSource[Char]]
      rec(const(0))
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

class EOFTermGrammar[E : Type] extends GrammarComputable[E,Unit] {
  def computesArity = 0
  def getComputesElement(n : Int) = throw IndexOutOfBoundsException(n.toString)
  def setComputesElement(n : Int, v : Computes[_]) = throw IndexOutOfBoundsException(n.toString)
  override def shallowClone = EOFTermGrammar()

  def tryFold = None
  def flatten =
    (input : Computes[InputSource[E]], success : Computes[SuccessFn[E,Unit]], shallowFail : Computes[ShallowFailFn], deepFail : Computes[DeepFailFn]) =>
      input(
        (e : Computes[E], i : Computes[Int], next : Computes[InputSource[E]]) =>
          shallowFail(const("not EOF")),
        (i : Computes[Int]) =>
          success(const(()), const(null)))
}

class AnyTermGrammar[E : Type] extends GrammarComputable[E,E] {
  def computesArity = 0
  def getComputesElement(n : Int) = throw IndexOutOfBoundsException(n.toString)
  def setComputesElement(n : Int, v : Computes[_]) = throw IndexOutOfBoundsException(n.toString)
  override def shallowClone = AnyTermGrammar()

  def tryFold = None
  def flatten =
    (input : Computes[InputSource[E]], success : Computes[SuccessFn[E,E]], shallowFail : Computes[ShallowFailFn], deepFail : Computes[DeepFailFn]) =>
      input(
        (e : Computes[E], i : Computes[Int], next : Computes[InputSource[E]]) =>
          success(e, next),
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

