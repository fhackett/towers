package towers

import Predef.{any2stringadd => _, _} // allow implicits to override +

import scala.compiletime._
import scala.quoted._

object Util {
  inline def dispatch[T](obj : =>Any, inline name : String)(params : =>Any*) : T =
    // FIXME: name should be passable as-is due to being inline
    // FIXME: isn't params by name? why do I have to get the underlying argument?
    ${ dispatchImpl[T]('{ obj }, '{ name }, '{ params }) }

  def dispatchImpl[T : Type](obj : Expr[Any], nameExpr : Expr[String], params : Expr[Seq[Any]]) with (qctx : QuoteContext) : Expr[T] = {
    import qctx.tasty.{_,given}
    val matching.Value(name) = nameExpr
    val id = unsafe.UnsafeExpr.underlyingArgument(obj).unseal
    println(s"${id.tpe}\n  ${id.show}\n  ${id.tpe.classSymbol}")
    val List(sym) = id.tpe.classSymbol.get.method(name)
    val matching.ExprSeq(paramExprs) = unsafe.UnsafeExpr.underlyingArgument(params)
    // TODO: make it possible to generate an empty Apply?
    val apply =
      if paramExprs.isEmpty
      then obj.unseal.select(sym)
      else Apply(obj.unseal.select(sym), paramExprs.map(_.unseal).toList)
    assert(apply.tpe <:< typeOf[T])
    apply.seal.asInstanceOf[Expr[T]]
  }

  def rec[T](t : T) : T = t

  inline def chase[T](t : =>T) : T =
    ${ chaseImpl('{ t }) }

  def chaseImpl[T](tExpr : Expr[T]) with (qctx : QuoteContext) : Expr[T] = {
    import qctx.tasty.{_,given}
    tExpr.unseal match {
      case Inlined(_, _, id) =>
        println(s"${id.show} ${id.symbol}")
        id.symbol.tree match {
          case ValDef(name, tpt, Some(rhs)) =>
            rhs.seal.asInstanceOf[Expr[T]]
        }
    }
  }

  inline def redMatch[H,T](h : =>H)(cases : =>PartialFunction[H,T]*) : T =
    ${ redMatchImpl[H,T]('{ h }, '{ cases }) }

  def redMatchImpl[H,T](hExpr : Expr[H], casesExpr : Expr[Seq[PartialFunction[H,T]]]) with (qctx : QuoteContext) : Expr[T] = {
    import qctx.tasty.{_,given}
    ???
  }
}

/*
trait Reducer[AST,Result] {
  //inline def apply(ast : =>AST) : Result
  inline def dispatch(ast : =>AST) : Result =
    ${ Reducer.dispatchImpl('{ this }, '{ ast }) }
}

object Reducer {
  def dispatchImpl[AST,Result](self : Expr[Reducer[AST,Result]], ast : Expr[AST]) with (qctx : QuoteContext) : Expr[Result] = {
    import qctx.tasty.{_,given}
    self.unseal match {
      case Inlined(_, _, id) =>
        val List(sym) = id.symbol.method("apply")
        Apply(self.unseal.select(sym), List(ast.unseal)).seal.asInstanceOf[Expr[Result]]
    }
  }
}*/

trait Parsers {

  sealed trait ParseResult[+T]
  case class ParseSuccess[T](val t : T, val rest : Input) extends ParseResult[T]
  case class ParseFailure(val msg : String) extends ParseResult[Nothing]
  case class ParseError(val msg : String) extends ParseResult[Nothing]

  type Input = Seq[Elem]
  type Elem

  inline def [T,P <: Parser[T]](self : =>P).apply(input : Input) : ParseResult[T] =
    Util.dispatch[ParseResult[T]](Util.chase(self), "reduce")(input)

  trait Parser[+T] {
    inline def |[U >: T](other : =>Parser[U]) <: Parser[U] =
      DisjunctionParser(this, other)

    inline def map[U](fn : =>(T=>U)) <: Parser[U] =
      flatMap(t => success(fn(t)))
    
    inline def flatMap[U](fn : =>(T=>Parser[U])) <: Parser[U] =
      FlatMapParser(this, fn)
  }

  inline def success[T](t : T) <: Parser[T] =
    SuccessParser(t)

  inline def literal(elem : =>Elem) <: Parser[Elem] =
    LiteralParser(elem)

  case class SuccessParser[T](val t : T) extends Parser[T] {
    inline def reduce(input : Input) : ParseResult[T] =
      ParseSuccess(t, input)
  }

  case class LiteralParser(val elem : Elem) extends Parser[Elem] {
    inline def reduce(input : Input) : ParseResult[Elem] = {
      val hd = input.head
      if hd == elem
      then ParseSuccess(hd, input.tail)
      else ParseFailure(hd.toString)
    }
  }

  case class DisjunctionParser[+T](val lhs : Parser[T], val rhs : Parser[T]) extends Parser[T] {
    inline def reduce(input : Input) : ParseResult[T] =
      lhs(input) match {
        case s : ParseSuccess[_] => s
        case ParseFailure(_) => rhs(input)
        case e : ParseError => e
      }
  }

  case class FlatMapParser[U,T](val parser : Parser[U], val fn : U=>Parser[T]) extends Parser[T] {
    inline def reduce(input : Input) : ParseResult[T] =
      parser(input) match {
        case ParseSuccess(result, rest) => fn(result)(rest)
        case f : ParseFailure => f
        case e : ParseError => e
      }
  }
}

