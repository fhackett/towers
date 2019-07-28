package towers.grammar

import quoted._

import towers.computes.{Computes,Computable,OpContext,KeyContext}
import Computes._


type Error = String

class InputSource[E](pc : Int, closure : Array[Any]) extends ==>[((E,Int,InputSource[E])==>Unit,Int|=>Unit),Unit](pc, closure)

type SFailFn = Error|=>Unit
type DFailFn = Error|=>Unit
type SSuccessFn[E,T] = (T,InputSource[E])==>Unit
type DSuccessFn[E,T] = (T,InputSource[E])==>Unit
type Grammar[E,T] = (InputSource[E],SSuccessFn[E,T],DSuccessFn[E,T],SFailFn,DFailFn)==>Unit

class Cell[T](var t : T)

object Grammar {

  implicit def InputSourceInst[E : Type] : Computes.FnInst[InputSource[E]] = new {
    def apply(pc : Expr[Int], closure : Expr[Array[Any]]) given QuoteContext = '{ InputSource(${ pc }, ${ closure }) }
  }

  def parse[E : Type, T : Type](g : Computes[Grammar[E,T]], input : Computes[InputSource[E]]) : Computes[Option[T]] =
    let(expr((), _ => '{ Cell[Option[T]](null) }), (cell : Computes[Cell[Option[T]]]) =>
        let(
          g(
            input,
            (t : Computes[T], _ : Computes[InputSource[E]]) => expr((cell, t), {
              case (cell, t) => '{ ${ cell }.t = Some(${ t }) }
            }),
            (t : Computes[T], _ : Computes[InputSource[E]]) => expr((cell, t), {
              case (cell, t) => '{ ${ cell }.t = Some(${ t }) }
            }),
            (_ : Computes[Error]) => expr1(cell, cell => '{ ${ cell }.t = None }),
            (_ : Computes[Error]) => expr1(cell, cell => '{ ${ cell }.t = None })),
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
      `try`(g.flatMap((t : Computes[T]) => fn(t).switch(List(const(true) -> succeed[E,T](t), const(false) -> fail[E,T](const("filter"))))))

    def rep(sep : Computes[Grammar[E,Unit]] = succeed(const(()))) : Computes[Grammar[E,Seq[T]]] = {
      import scala.collection.mutable.ArrayBuffer
      // TODO: rewrite in terms of ArrayBuffer, currently that breaks codegen

      lazy val rec : Computes[Seq[T]|=>Grammar[E,Seq[T]]] =
        (buf : Computes[Seq[T]]) =>
          choose(
            for(t : Computes[T] <- `try`(
                  for(_ : Computes[Unit] <- sep;
                      t : Computes[T] <- ref(g))
                    yield t);
                b2 : Computes[Seq[T]] <- ref(rec).apply(expr((buf, t), {
                  case (buf, t) => '{ ${ buf } :+ ${ t } }
                })))
              yield b2,
            succeed(buf))

      choose(
        for(t : Computes[T] <- `try`(ref(g));
            b2 : Computes[Seq[T]] <- ref(rec).apply(expr1(t, t => '{ Seq(${ t })/*ArrayBuffer[T]() +=${ t }*/ })))
          yield b2,
        succeed(expr((), _ => '{ Seq.empty })))
    }

    def repDrop(sep : Computes[Grammar[E,Unit]] = succeed(const(()))) : Computes[Grammar[E,Unit]] = {
      lazy val rec : Computes[Grammar[E,Unit]] =
        choose(
          `try`(sep.flatMap((_ : Computes[Unit]) => ref(g))).flatMap((_ : Computes[T]) => ref(rec)),
          succeed(const(())))

      choose(
        ref(g).flatMap((_ : Computes[T]) => ref(rec)),
        succeed(const(())))
    }
  }

  implicit class IndexedSeqOps[E : Type, S <: IndexedSeq[E] : Type](seq : Computes[S]) {
    def length : Computes[Int] =
      expr1(seq, seq => '{ ${ seq }.length })
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
            expr1(input, input => '{ ${ input }.length }).switch(
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

class TermGrammar[E : Type](val term : Computes[E]) extends GrammarComputable[E,E] {

  def toComputesSeq = Seq(term)
  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = seq match {
    case Seq(term : Computes[E]) => TermGrammar(term)
  }

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
  def flatten =
    (input : Computes[InputSource[E]], sSuccess : Computes[SSuccessFn[E,E]], dSuccess : Computes[DSuccessFn[E,E]], sFail : Computes[SFailFn], dFail : Computes[DFailFn]) =>
      input(
        ((e : Computes[E], i : Computes[Int], next : Computes[InputSource[E]]) =>
          e.switch(
            List(term -> dSuccess(e, next)),
            default=sFail(const("error")))) : Computes[(E,Int,InputSource[E])==>Unit],
        ((i : Computes[Int]) =>
          sFail(const("eof"))) : Computes[Int|=>Unit])
}

class EOFTermGrammar[E : Type] extends GrammarComputable[E,Unit] {

  def toComputesSeq = Seq.empty
  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = seq match {
    case Seq() => EOFTermGrammar()
  }

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
  def flatten =
    (input : Computes[InputSource[E]], sSuccess : Computes[SSuccessFn[E,Unit]], dSuccess : Computes[DSuccessFn[E,Unit]], sFail : Computes[SFailFn], dFail : Computes[DFailFn]) =>
      input(
        (e : Computes[E], i : Computes[Int], next : Computes[InputSource[E]]) =>
          sFail(const("not EOF")),
        (i : Computes[Int]) =>
          sSuccess(const(()), const(null)))
}

class AnyTermGrammar[E : Type] extends GrammarComputable[E,E] {

  def toComputesSeq = Seq.empty
  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = seq match {
    case Seq() => AnyTermGrammar()
  }

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
  def flatten =
    (input : Computes[InputSource[E]], sSuccess : Computes[SSuccessFn[E,E]], dSuccess : Computes[DSuccessFn[E,E]], sFail : Computes[SFailFn], dFail : Computes[DFailFn]) =>
      input(
        (e : Computes[E], i : Computes[Int], next : Computes[InputSource[E]]) =>
          dSuccess(e, next),
        ((i : Computes[Int]) =>
          sFail(const("eof"))) : Computes[Int|=>Unit])
}

class SuccessGrammar[E : Type, T : Type](var t : Computes[T]) extends GrammarComputable[E,T] {
  
  def toComputesSeq = Seq(t)
  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = seq match {
    case Seq(t : Computes[T]) => SuccessGrammar(t)
  }

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
  def flatten =
    (input : Computes[InputSource[E]], sSuccess : Computes[SSuccessFn[E,T]], dSuccess : Computes[DSuccessFn[E,T]], sFail : Computes[SFailFn], dFail : Computes[DFailFn]) =>
      sSuccess(t, input)
}

class FailGrammar[E : Type, T : Type](var err : Computes[Error]) extends GrammarComputable[E,T] {
  
  def toComputesSeq = Seq(err)
  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = seq match {
    case Seq(err : Computes[Error]) => FailGrammar(err)
  }

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
  def flatten =
    (input : Computes[InputSource[E]], sSuccess : Computes[SSuccessFn[E,T]], dSuccess : Computes[DSuccessFn[E,T]], sFail : Computes[SFailFn], dFail : Computes[DFailFn]) =>
      sFail(err)
}

class FlatMapGrammar[E : Type, T1 : Type, T2 : Type](var g : Computes[Grammar[E,T1]], var fn : Computes[T1|=>Grammar[E,T2]]) extends GrammarComputable[E,T2] {

  def toComputesSeq = Seq(g, fn)
  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = seq match {
    case Seq(g : Computes[Grammar[E,T1]], fn : Computes[T1|=>Grammar[E,T2]]) => FlatMapGrammar(g, fn)
  }

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
  def flatten =
    (input : Computes[InputSource[E]], sSuccess : Computes[SSuccessFn[E,T2]], dSuccess : Computes[DSuccessFn[E,T2]], sFail : Computes[SFailFn], dFail : Computes[DFailFn]) =>
      g(
        input,
        (t1 : Computes[T1], next : Computes[InputSource[E]]) =>
          fn(t1).apply(next, sSuccess, dSuccess, sFail, dFail),
        (t1 : Computes[T1], next : Computes[InputSource[E]]) =>
          fn(t1).apply(next, dSuccess, dSuccess, dFail, dFail),
        sFail,
        dFail)
}

class DisjunctGrammar[E : Type, T : Type](var left : Computes[Grammar[E,T]], var right : Computes[Grammar[E,T]]) extends GrammarComputable[E,T] {
  
  def toComputesSeq = Seq(left, right)
  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = seq match {
    case Seq(left : Computes[Grammar[E,T]], right : Computes[Grammar[E,T]]) => DisjunctGrammar(left, right)
  }

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
  def flatten =
    (input : Computes[InputSource[E]], sSuccess : Computes[SSuccessFn[E,T]], dSuccess : Computes[DSuccessFn[E,T]], sFail : Computes[SFailFn], dFail : Computes[DFailFn]) =>
      left(
        input,
        sSuccess,
        dSuccess,
        (error : Computes[Error]) =>
          right(input, sSuccess, dSuccess, sFail, dFail),
        dFail)
}

class TryGrammar[E : Type, T : Type](var g : Computes[Grammar[E,T]]) extends GrammarComputable[E,T] {
  
  def toComputesSeq = Seq(g)
  def likeFromSeq(seq : Seq[_ <: Computes[_]])(implicit keyCtx : KeyContext) = seq match {
    case Seq(g : Computes[Grammar[E,T]]) => TryGrammar(g)
  }

  def tryFold(implicit opCtx : OpContext, keyCtx : KeyContext) = None
  def flatten =
    (input : Computes[InputSource[E]], sSuccess : Computes[SSuccessFn[E,T]], dSuccess : Computes[DSuccessFn[E,T]], sFail : Computes[SFailFn], dFail : Computes[DFailFn]) =>
      g(input, sSuccess, dSuccess, sFail, sFail)
}

object Test {
  
  def mkStringParser[T : Type](g : Computes[Grammar[Char,T]]) : Computes[String|=>Option[T]] =
    (str : Computes[String]) =>
      Grammar.parse(g, Grammar.makeStringInput(str))

  val aSeq : Computes[Grammar[Char,Seq[Char]]] =
    term('a').rep()

  inline def matchEOF(str : String) : Option[Unit] = ${ Computes.reifyCall(mkStringParser(eofTerm), '{ str }) }
  inline def matchAs(str : String) : Option[Seq[Char]] = ${ Computes.reifyCall(mkStringParser(aSeq), '{ str }) }
}

