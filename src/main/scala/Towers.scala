package towers

import Predef.{any2stringadd => _, _} // allow implicits to override +

import scala.collection.mutable.{HashMap, HashSet, ArrayStack, ArrayBuffer}
import scala.collection.immutable.TreeSet
//import scala.util.control.TailCalls._

import scala.deriving._
import scala.quoted._
import scala.tasty._
import scala.compiletime._
import scala.reflect._

object Meta {
  trait Uninterpreted[T]
  def rewrite[T](t : T)(fn : T=>T) : T = ???
}

object Compiler {

  given Meta.Uninterpreted[Int]

  def compileImpl[T](expr : Expr[T])(given qctx : QuoteContext) : Expr[T] = {
    import qctx.tasty.{_,given}

    sealed abstract class VRef
    object VRef {
      private var nextID = 0
      private case class VRefSym(val sym : Symbol) extends VRef
      private case class VRefAnon(val id : Int, val pos : Position) extends VRef
      def gen(pos : Position) : VRef =
        VRefAnon({val tmp = nextID; nextID += 1; tmp}, pos)
      def apply(sym : Symbol) : VRef =
        VRefSym(sym)
    }

    sealed abstract class VTerm
    case class KnownLiteral(val v : Any) extends VTerm
    case class KnownPattern(val head : Symbol, val members : List[ProcResult]) extends VTerm
    case class IndirectVTerm(val key : VRef) extends VTerm
    case class TransientApplicable(val params : List[VRef], val body : ProcResult) extends VTerm
    case object OpaqueApplicable extends VTerm

    // return symbolic tree as transformed as possible
    // bindings are arbitrary points where a rewrite was or can be performed (rebound on rewrite)
    // rewriteHooks is a mapping from VRefs of interest to rewrite hooks that could react to changes at those VRefs
    //  these can change if an inlining is performed, allowing embedded rewrites to react to new knowledge about bound vars
    //  these can also change as a transitive result of some other rewrite rule, which is why keys are either Sym or Anon
    // full tree as it is "now" can be requested by passing in a mapping from VRef to Term
    //  (any remaining function arguments or val bindings will need to introduce their own bindings as they go)
    // include vector/map/set that accumulates functions known to be recursive

    case class ResultData(val foundRecursive : Set[Symbol] = Set.empty)

    trait ProcResult {
      val data : ResultData
      val term : VTerm
      def mkTerm(bindings : Map[VRef,Term]) : Term
    }

    def procTerm(term : Term, visitingSyms : Set[Symbol], knownSyms : Map[Symbol,ProcResult]) : ProcResult = term match {
      case Inlined(call, bindings, body) =>
        new ProcResult {
          val innerResult = procTerm(body, visitingSyms, knownSyms)
          val data = innerResult.data
          val term = innerResult.term
          def mkTerm(b : Map[VRef,Term]) =
            Inlined(call, bindings, innerResult.mkTerm(b))
        }
      case l @ Literal(v) =>
        new ProcResult {
          val data = ResultData()
          val term = KnownLiteral(v)
          def mkTerm(bindings : Map[VRef,Term]) = l
        }
      case Block(statements, expr) => {
        error("TODO", term.pos)
        ???
      }
      case Apply(fun, args) => {
        val pfn = procTerm(fun, visitingSyms, knownSyms)
        val pargs = args.map(procTerm(_, visitingSyms, knownSyms))
        pfn.term match {
          case TransientApplicable(params, body) =>
            new ProcResult {
              val data = body.data
              val term = body.term
              def mkTerm(bindings : Map[VRef,Term]) =
                body.mkTerm(bindings ++ (params zip pargs.map(_.mkTerm(bindings))))
            }
        }
      }
      case select @ Select(base, name) => {
        val sym = select.symbol
        val tpe = base.tpe.widen.seal.asInstanceOf[quoted.Type[Any]]
        searchImplicit('[Meta.Uninterpreted[${tpe}]].unseal.tpe) match {
          case success : ImplicitSearchSuccess =>
            new ProcResult {
              val baseResult = procTerm(base, visitingSyms, knownSyms)
              val data = baseResult.data
              val term = OpaqueApplicable
              def mkTerm(bindings : Map[VRef,Term]) =
                Select(baseResult.mkTerm(bindings), sym)
            }
          case no : NoMatchingImplicits =>
            if( sym.isDefDef ) {
              if( visitingSyms(sym) ) {
                ???
              } else {
                sym.tree match {
                  case DefDef(name, Nil, Nil, returnTpt, Some(rhs)) =>
                    procTerm(rhs, visitingSyms + sym, knownSyms)
                  case DefDef(name, Nil, List(params), returnTpt, Some(rhs)) => {
                    val bodyResult = procTerm(rhs, visitingSyms + sym, knownSyms)
                    new ProcResult {
                      val data = bodyResult.data
                      val term = TransientApplicable(params.map(vdef=>VRef(vdef.symbol)), bodyResult)
                      def mkTerm(bindings : Map[VRef,Term]) = ??? // must disappear?
                    }
                  }
                }
              }
            } else {
              error("TODO", term.pos)
              ???
            }
        }
      }
      case id : Ident =>
        knownSyms.get(id.symbol) match {
          case Some(known) =>
            new ProcResult {
              val data = known.data
              val term = known.term
              def mkTerm(bindings : Map[VRef,Term]) =
                bindings(VRef(id.symbol))
            }
          case None => {
            error("TODO", term.pos)
            ???
          }
        }
    }

    procTerm(expr.unseal, Set.empty, Map.empty).mkTerm(Map.empty).seal.asInstanceOf[Expr[T]]
  }

  inline def compile[T](expr : =>T) : T =
    ${ compileImpl('{ expr }) }

}

