package polyparse

import scala.collection.immutable.Set
import scala.quoted._
import scala.quoted.Toolbox.Default._

sealed abstract class ParseResult[Result]
case class ParseSuccess[Result](result : Result) extends ParseResult[Result]
case class ParseFailure[Result](position : Int, message : String) extends ParseResult[Result]

private case class GrammarContext[SeqType,A](
  next : Expr[Unit],
  read : Expr[A],
  mark : Expr[Int],
  restore : Expr[Int] => Expr[Unit],
  seq : Expr[SeqType],
  isEOF : Expr[Boolean],
  rec : Map[Grammar[_,_,_],Any],
)

sealed private trait UnguardedGrammar[Result : Type, SeqType <: Seq[A], A : Type] {
  def capture(ctx : GrammarContext[SeqType, A])(implicit st : Type[SeqType]) : Expr[Option[Result]]
  //def check(ctx : GrammarContext[SeqType, A])(implicit st : Type[SeqType]) : Expr[Boolean]
}

sealed class Grammar[Result : Type, SeqType <: Seq[A], A : Type](g : =>UnguardedGrammar[Result, SeqType, A]) extends UnguardedGrammar[Result, SeqType, A] {
  def parser(implicit st : Type[SeqType]) : Expr[SeqType => Option[Result]] = '{
    (seq : SeqType) => {
      var i = 0;
      ~capture(GrammarContext(
        next='(i += 1),
        read='(seq(i)),
        mark='(i),
        restore=(r : Expr[Int]) => '(i = ~r),
        seq='(seq),
        isEOF='(i >= seq.length),
        rec=Map(),
      ))
    }
  }
  
  def capture(ctx : GrammarContext[SeqType, A])(implicit st : Type[SeqType]) : Expr[Option[Result]] =
    ctx.rec.get(this) match {
      case Some(recursion) => '{
        val (cap : Option[Result], ii : Int) = (~recursion.asInstanceOf[Expr[(SeqType, Int) => (Option[Result], Int)]])(~ctx.seq, ~ctx.mark);
        ~ctx.restore('(ii));
        cap
      }
      case None => '{
        def self(seq : SeqType, outerI : Int) : (Option[Result], Int) = {
          var i = outerI;
          val cap = ~g.capture(GrammarContext(
            next='(i += 1),
            read='(seq(i)),
            mark='(i),
            restore=(r : Expr[Int]) => '(i = ~r),
            seq='(seq),
            isEOF='(i >= seq.length),
            rec=ctx.rec.+((this, '(self))),
          ));
          (cap, i)
        }
        ~g.capture(GrammarContext(
          next=ctx.next,
          read=ctx.read,
          mark=ctx.mark,
          restore=ctx.restore,
          seq=ctx.seq,
          isEOF=ctx.isEOF,
          rec=ctx.rec.+((this, '(self))),
        ))
      }
    }
  
  //def check(ctx : GrammarContext[SeqType, A])(implicit st : Type[SeqType]) : Expr[Boolean]
}

object Implicits {
  import scala.language.implicitConversions

  implicit def makeGuarded[Result : Type, SeqType <: Seq[A], A : Type](g : =>UnguardedGrammar[Result, SeqType, A]) : Grammar[Result, SeqType, A] =
    new Grammar(g)
}

case class exactly[SeqType <: Seq[A], A : Liftable : Type](v : A) extends UnguardedGrammar[A,SeqType,A] {
  def capture(ctx : GrammarContext[SeqType, A])(implicit st : Type[SeqType]) : Expr[Option[A]] =
    '{ val r = ~ctx.read; if (r == ~(v.toExpr)) { ~ctx.next; Some(r) } else None }

  /*def check(ctx : GrammarContext[A], rec : Set[Any])(implicit st : Type[SeqType]) : Expr[Boolean] =
    '{ if (~ctx.read == ~(v.toExpr)) { ~ctx.next; true } else false } */
}

