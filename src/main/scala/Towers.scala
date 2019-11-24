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

object LazyTree {
  sealed abstract class Value[T] {
    final def map[T2](fn : T=>T2) : Value[T2] =
      flatMap(value => Value(fn(value)))
    final def flatMap[T2](fn : T=>Value[T2]) : Value[T2] =
      FlatMapValue(this, fn)
    final def updated[V](from : Value[V], to : V) : Value[T] =
      UpdatedValue(this, from, to)

    def result : T = {
      case class Result(val results : Map[Value[_],Any] = Map.empty, val dependencies : Map[Value[_],Set[Value[_]]] = Map.empty) {
        def updated[V](name : Value[V], value : V) : Result =
          copy(results.updated(name, value))
        def alias[V](name : Value[V], value : Value[V]) : Result =
          copy(results=results + ((name, results(value))))
        def dependsOn(deriving : Value[_], base : Value[_]) : Result =
          copy(dependencies=dependencies + ((base, listDependsOn(base) + deriving)))
        def listDependsOn(key : Value[_]) : Set[Value[_]] =
          dependencies.getOrElse(key, Set.empty)
        def without(keys : Iterable[Value[_]]) : Result =
          copy(results=results -- keys)
      }

      // avoid potentially blowing stack when computing the result
      import scala.util.control.TailCalls._

      def impl[T](self : Value[T], resultSoFar : Result) : TailRec[Result] =
        if( resultSoFar.results.contains(self) ) {
          done(resultSoFar)
        } else {
          self match {
            case self : ConstValue[T] =>
              done(resultSoFar.updated(self, self.value()))
            case self : FlatMapValue[t1,T] => {
              tailcall(impl(self.from, resultSoFar)).flatMap { result1 =>
                val next = self.fn(result1.results(self.from).asInstanceOf[t1])
                tailcall(impl(next, result1.dependsOn(next,self.from))).map { result2 =>
                  result2.dependsOn(self, next).alias(self, next)
                }
              }
            }
            case self : UpdatedValue[T,v] => {
              // calculate closure of all dependencies of the value we propose to change
              def findAllDepends(listDependsOn : Value[_]=>Set[Value[_]], key : Value[_], found : Set[Value[_]]) : Set[Value[_]] = {
                val deps = listDependsOn(key).filter(!found(_))
                val innerFound = deps ++ found
                deps ++ deps.flatMap(dep => findAllDepends(listDependsOn, dep, innerFound))
              }
              val allDepends = findAllDepends(resultSoFar.listDependsOn, self.key, Set.empty)
              // wipe all dependencies of the changed value, then set the new value (in case the value depends on itself)
              // then we can calculate only what we need of the body, possibly recalculating nullified dependencies
              tailcall(impl(self.over, resultSoFar.without(allDepends).updated(self.key, self.value)))
                .map(_.alias(self, self.over).dependsOn(self, self.over)).map { result =>
                // now, to preserve the declarative evaluation (referring to the updated tree again without the Updates)
                // we clean up all self.key's dependencies, leaving only our own result
                val value = result.results(self).asInstanceOf[T]
                // make sure to recalculate deps, you might have gained some
                val allDependsAfter = findAllDepends(result.listDependsOn, self.key, Set.empty)
                result.without(allDependsAfter + self.key).updated(self, value)
                // performance thoughts: it is reasonably cheap to purge all the potentially invalid cached values
                // if something needs recomputing it will happen later, if at all
                // slowdown would come from having many deep dependency networks, in the order of how many nodes depend on what
                // you're changing
                // if you don't change anything you get normal performance, if you do you may have to recompute dependent trees
              }
            }
          }
        }

      impl(this, Result()).result.results(this).asInstanceOf[T]
    }
  }
  object Value {
    def apply[T](value : =>T) : Value[T] =
      ConstValue(()=>value)
  }
  private class ConstValue[T](val value : ()=>T) extends Value[T]
  private class FlatMapValue[T1,T2](val from : Value[T1], val fn : T1=>Value[T2]) extends Value[T2]
  private class UpdatedValue[T,V](val over : Value[T], val key : Value[V], val value : V) extends Value[T]
}

object Compiler {

  given Meta.Uninterpreted[Int]

  def compileImpl[T](expr : Expr[T])(given qctx : QuoteContext) : Expr[T] = {
    import qctx.tasty.{_,given}
    import LazyTree.Value

    sealed abstract class InferredInfo
    object InferredInfo {
      case object Opaque extends InferredInfo
      case class Literal(val v : Any) extends InferredInfo
      case class Inlineable(val params : List[Value[ProcResult]], val body : Value[ProcResult]) extends InferredInfo
    }

    // return symbolic tree as transformed as possible
    // bindings are arbitrary points where a rewrite was or can be performed (rebound on rewrite)
    // rewriteHooks is a mapping from VRefs of interest to rewrite hooks that could react to changes at those VRefs
    //  these can change if an inlining is performed, allowing embedded rewrites to react to new knowledge about bound vars
    //  these can also change as a transitive result of some other rewrite rule, which is why keys are either Sym or Anon
    // full tree as it is "now" can be requested by passing in a mapping from VRef to Term
    //  (any remaining function arguments or val bindings will need to introduce their own bindings as they go)
    // include vector/map/set that accumulates functions known to be recursive

    trait ProcResult {
      val referencedSymbols : Value[Set[Symbol]]
      val inferredInfo : Value[InferredInfo]
      val term : Value[Term]
      val definitions : Value[Vector[Statement]]
    }

    def procTerm(term : Term, knownSyms : Map[Symbol,Value[ProcResult]]) : Value[ProcResult] = {
      println(s"!! $term")
      term match {
        case Inlined(call, bindings, body) =>
          procTerm(body, knownSyms).map { result =>
            new ProcResult {
              val referencedSymbols = result.referencedSymbols
              val inferredInfo = result.inferredInfo
              val term = result.term.map { term =>
                Inlined(call, bindings, term)
              }
              val definitions = result.definitions
            }
          }
        case l @ Literal(v) =>
          Value {
            new ProcResult {
              val referencedSymbols = Value(Set.empty)
              val inferredInfo = Value(InferredInfo.Literal(v))
              val term = Value(l)
              val definitions = Value(Vector.empty)
            }
          }
        case Block(statements, expr) => {
          error("TODO", term.pos)
          ???
        }
        case Apply(fun, args) => {
          val argResults : List[Value[ProcResult]] = args.map(procTerm(_, knownSyms))
          val argReferencedSymbols = argResults.foldLeft(Value(Set.empty[Symbol])) { (acc, argResult) =>
            acc.flatMap { accVal =>
              argResult.flatMap(argResult => argResult.referencedSymbols.map(refs => accVal ++ refs))
            }
          }
          procTerm(fun, knownSyms).flatMap { fnResult =>
            fnResult.inferredInfo.map {
              // TODO: inlining if we deduce that we can
              case _ =>
                new ProcResult {
                  val referencedSymbols = fnResult.referencedSymbols.flatMap { fnSyms =>
                    argReferencedSymbols.map(argSyms => fnSyms ++ argSyms)
                  }
                  val inferredInfo = Value(InferredInfo.Opaque)
                  val term = fnResult.term.flatMap { fnTerm =>
                    argResults.foldLeft(Value(Nil) : Value[List[Term]]) { (acc, argResult) =>
                      acc.flatMap { acc =>
                        argResult.flatMap( argResult => argResult.term.map(t => t :: acc))
                      }
                    }.map { argTerms =>
                      Apply(fnTerm, argTerms.reverse)
                    }
                  }
                  val definitions = fnResult.definitions.flatMap { fnDefinitions =>
                    argResults.foldLeft(Value(fnDefinitions)) { (acc, argResult) =>
                      acc.flatMap { acc =>
                        argResult.flatMap( argResult => argResult.definitions.map(ds => acc ++ ds))
                      }
                    }
                  }
                }
            }
          }
        }
        case select @ Select(base, name) => {
          val sym = select.symbol
          knownSyms.get(sym) match {
            case Some(result) => result
            case None => {
              val tpe = base.tpe.widen.seal.asInstanceOf[quoted.Type[Any]]
              searchImplicit('[Meta.Uninterpreted[${tpe}]].unseal.tpe) match {
                case _ : ImplicitSearchSuccess =>
                  procTerm(base, knownSyms).map { baseResult =>
                    new ProcResult {
                      val referencedSymbols = baseResult.referencedSymbols
                      val inferredInfo = Value(InferredInfo.Opaque)
                      val term = baseResult.term.map { baseTerm =>
                        Select(baseTerm, sym)
                      }
                      val definitions = baseResult.definitions
                    }
                  }
                case _ : NoMatchingImplicits =>
                  if( sym.isDefDef ) {
                    val tree = sym.tree.asInstanceOf[DefDef]
                    val paramResults : Map[Symbol,Value[ProcResult]] = tree.paramss.flatMap(_.map { param =>
                      (param.symbol, Value {
                        new ProcResult {
                          val referencedSymbols = Value(Set(param.symbol))
                          val inferredInfo = Value(InferredInfo.Opaque)
                          val term = Value(Ref(param.symbol))
                          val definitions = Value(Vector.empty)
                        }
                      })
                    }).toMap
                    val recSelf = new ProcResult {
                      val referencedSymbols = Value(Set(sym))
                      val inferredInfo = Value(InferredInfo.Opaque)
                      val term = Value('{???}.unseal)
                      val definitions = Value(Vector.empty)
                    }
                    procTerm(tree.rhs.get, knownSyms ++ paramResults + ((sym, Value(recSelf)))).flatMap { bodyResult =>
                      bodyResult.referencedSymbols.map { refSymbols =>
                        // TODO: if( refSymbols(sym) ) {
                        new ProcResult {
                          val referencedSymbols = bodyResult.referencedSymbols
                          val inferredInfo = Value(InferredInfo.Opaque) // TODO: or inlineable
                          val definition = bodyResult.term.map { bodyTerm =>
                            DefDef.copy(tree)(sym.fullName, Nil /*TODO: handle type params*/, tree.paramss, tree.returnTpt, Some(bodyTerm))
                          }
                          val term = definition.map { defn =>
                            Ref(defn.symbol)
                          }
                          val definitions = bodyResult.definitions.flatMap { bodyDefs =>
                            definition.map(d => bodyDefs :+ d)
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
          }
        }
        case id : Ident =>
          knownSyms.get(id.symbol) match {
            case Some(result) => result
            case None => {
              error("TODO", term.pos)
              ???
            }
          }
      }
    }

    procTerm(expr.unseal, Map.empty).flatMap { result =>
      result.definitions.flatMap { defns =>
        result.term.map { term =>
          val block : Expr[T] = Block(defns.toList, term).seal.asInstanceOf[Expr[T]]
          println(block.show)
          block
        }
      }
    }.result
  }

  inline def compile[T](expr : =>T) : T =
    ${ compileImpl('{ expr }) }

}

