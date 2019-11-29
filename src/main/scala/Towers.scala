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
      final case class Result(val results : Map[Value[_],Any] = Map.empty, val dependencies : Map[Value[_],Set[Value[_]]] = Map.empty, val flatCache : Map[(Value[_],Any),Value[_]] = Map.empty) {
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

        def getFlatCached[T1,T2](self : Value[T2], v : T1) : Option[Value[T2]] =
          flatCache.get((self,v)).asInstanceOf[Option[Value[T2]]]
        def cacheFlat[T1,T2](self : Value[T2], value : T1, next : Value[T2]) : Result =
          copy(flatCache=flatCache + (((self,value), next)))
      }

      // avoid potentially blowing stack when computing the result
      import scala.util.control.TailCalls._

      var hitCount = 0

      def impl[T](self : Value[T], resultSoFar : Result) : TailRec[Result] =
        if( resultSoFar.results.contains(self) ) {
          done(resultSoFar)
        } else {
          hitCount += 1
          self match {
            case self : ConstValue[T] =>
              done(resultSoFar.updated(self, self.value()))
            case self : FlatMapValue[t1,T] => {
              tailcall(impl(self.from, resultSoFar)).flatMap { result1 =>
                // cache flatMap results, since if the value is the same then the next tree should not be changing
                // note: this combined with not establishing a dependency between value and projected next allows
                //  us to quietly swallow internal changes that do not actually affect the resulting value
                val (result2, next) = result1.getFlatCached(self, result1.results(self.from)) match {
                  case Some(next) => (result1, next)
                  case None => {
                    val value = result1.results(self.from).asInstanceOf[t1]
                    val nxt = self.fn(value)
                    (result1.cacheFlat(self, value, nxt), nxt)
                  }
                }
                tailcall(impl(next, result2)).map { result3 =>
                  result3.dependsOn(self, self.from).dependsOn(self, next).alias(self, next)
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

      val res = impl(this, Result()).result.results(this).asInstanceOf[T]
      println(s"PERF HITS $hitCount")
      //(new Throwable).printStackTrace()
      res
    }
  }
  object Value {
    def apply[T](value : =>T) : Value[T] =
      ConstValue(()=>value)

    def lifted[T, I[_] <: Iterable[_]](values : I[Value[T]]) : Value[I[T]] = {
      val factory = values.iterableFactory
      values.foldLeft(Value(Nil : List[T])) { (acc, v) =>
        acc.flatMap { acc =>
          v.asInstanceOf[Value[T]].map(v => v :: acc)
        }
      }.map(rList => factory.from(rList.reverse).asInstanceOf[I[T]])
    }
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
      case class Inlineable(
        // definition, value used by fn, arg value
        val knownParams : List[(ValDef,Value[ProcResult],Value[ProcResult])],
        // definition, value used by fn
        val unknownParams : List[List[(ValDef,Value[ProcResult])]],
        val body : Value[ProcResult]
      ) extends InferredInfo
    }

    trait ProcResultDef {
      val referencedSymbols : Value[Set[Symbol]]
      val inferredInfo : Value[InferredInfo]
      val term : Value[Term]
      val definitions : Value[Vector[Statement]]
    }

    case class ProcResult(
      val referencedSymbols : Value[Set[Symbol]],
      val inferredInfo : Value[InferredInfo],
      val term : Value[Term],
      val definitions : Value[Vector[Statement]]
    ) extends ProcResultDef

    def mkResult(d : ProcResultDef) : ProcResult =
      ProcResult(
        referencedSymbols=d.referencedSymbols,
        inferredInfo=d.inferredInfo,
        term=d.term,
        definitions=d.definitions)

    def procDefDef(tree : DefDef, knownSyms : Map[Symbol,Value[ProcResult]]) : Value[(ProcResult,Value[DefDef])] = {
      val sym = tree.symbol
      val unknownParams : List[List[(ValDef,Value[ProcResult])]] = tree.paramss.map(_.map { param =>
        (param, Value(mkResult(new {
          val referencedSymbols = Value(Set(param.symbol))
          val inferredInfo = Value(InferredInfo.Opaque)
          val term = Value(Ref(param.symbol))
          val definitions = Value(Vector.empty)
        })))
      })
      val paramResults : Map[Symbol,Value[ProcResult]] = unknownParams.flatMap(_.map(p => (p._1.symbol, p._2))).toMap
      val tpe = tree.returnTpt.tpe.seal.asInstanceOf[quoted.Type[Any]]
      val methodWithoutBody : DefDef =
        '{
          def ifYouAreSeeingThisSomethingBroke : ${tpe} = ???
        }.unseal match {
          case Inlined(_, _, Block(List(theDefDef), _)) =>
            DefDef.copy(theDefDef)(sym.fullName, tree.typeParams, tree.paramss, tree.returnTpt, None)
        }
      val recSelf = mkResult(new {
        val referencedSymbols = Value(Set(sym))
        val inferredInfo = Value(InferredInfo.Opaque)
        val term = Value(Ref(methodWithoutBody.symbol))
        val definitions = Value(Vector.empty)
      })
      procTerm(tree.rhs.get, knownSyms ++ paramResults + ((sym, Value(recSelf)))).flatMap { bodyResult =>
        bodyResult.referencedSymbols.map { refSymbols =>
          val methodWithBody = bodyResult.term.map { bodyTerm =>
            DefDef.copy(methodWithoutBody)(
              sym.fullName, tree.typeParams, tree.paramss, tree.returnTpt, Some(bodyTerm))
          }
          // not-recursive def with no () must be inlined at Select, because there will be no Apply to catch inlining later
          if( tree.paramss.isEmpty && !refSymbols(sym) ) {
            (bodyResult, methodWithBody)
          } else {
            val result = mkResult(new {
              val referencedSymbols = bodyResult.referencedSymbols
              val inferredInfo =
                if( refSymbols(sym) ) {
                  // it's recursive, so pretend we don't know what it is
                  Value(InferredInfo.Opaque)
                } else {
                  Value(InferredInfo.Inlineable(
                    knownParams=Nil,
                    unknownParams=unknownParams,
                    body=Value(bodyResult)
                  ))
                }
              val term = methodWithBody.map { methodWithBody => Ref(methodWithBody.symbol) }
              val definitions = bodyResult.definitions
            })
            (result, methodWithBody)
          }
        }
      }
    }

    def procTerm(term : Term, knownSyms : Map[Symbol,Value[ProcResult]]) : Value[ProcResult] = {
      println(s"!! $term")
      term match {
        case Inlined(call, bindings, body) =>
          procTerm(body, knownSyms).map { result =>
            mkResult(new {
              val referencedSymbols = result.referencedSymbols
              val inferredInfo = result.inferredInfo
              val term = result.term.map { term =>
                Inlined(call, bindings, term)
              }
              val definitions = result.definitions
            })
          }
        case l @ Literal(v) =>
          Value {
            mkResult(new {
              val referencedSymbols = Value(Set.empty)
              val inferredInfo = Value(InferredInfo.Literal(v))
              val term = Value(l)
              val definitions = Value(Vector.empty)
            })
          }
        case Block(statements, expr) => {
          // start with bottom assumption: everything recursive via everything else. refine via updates.
          val allDefSyms : Set[Symbol] = statements.collect { case d : DefDef => d.symbol }.toSet
          val allDefs : List[(Symbol,Value[ProcResult])] = statements.collect {
            case d : DefDef => (d.symbol, Value(mkResult(new {
              val referencedSymbols = Value(allDefSyms)
              val inferredInfo = Value(InferredInfo.Opaque)
              val term = Value(Ref(d.symbol))
              val definitions = Value(Vector.empty)
            })))
          }
          // TODO: gradually replace unknowns with knowns over iteration, not at the end?
          val (innerSyms, blockStmts) = statements.foldLeft((knownSyms ++ allDefs, Value(Vector.empty[Statement]))) { (acc, stmt) =>
            acc match {
              case (knownSyms, prevStmts) =>
                stmt match {
                  case d @ DefDef(name, typeParams, paramss, tpt, Some(rhs)) => {
                    val result = procDefDef(d, knownSyms)
                    Tuple2(
                      knownSyms.updated(d.symbol, result.map(_._1)),
                      for {
                        stmts <- prevStmts
                        result <- result
                        ddef <- result._2
                      } yield stmts :+ ddef)
                  }
                  case d @ ValDef(name, tpt, Some(rhs)) => {
                    val rhsResultVal = procTerm(rhs, knownSyms)
                    Tuple2(
                      knownSyms.updated(d.symbol, rhsResultVal),
                      for {
                        stmts <- prevStmts
                        rhsResult <- rhsResultVal
                        term <- rhsResult.term
                      } yield stmts :+ ValDef.copy(d)(name, tpt, Some(term)))
                  }
                  case _ => error("TODO", term.pos); ???
                }
            }
          }
          val result =
            for {
              stmts <- blockStmts
              exprResult <- procTerm(expr, innerSyms)
            } yield mkResult(new {
              val referencedSymbols = exprResult.referencedSymbols
              val inferredInfo = exprResult.inferredInfo
              val term = exprResult.term.map { exprTerm =>
                Block(stmts.toList, exprTerm)
              }
              val definitions = exprResult.definitions
            })
          // ensure all definitions / folding takes into account our new-found knowledge
          allDefs.foldLeft(result) { (acc, symDef) =>
            val (sym, ddef) = symDef
            innerSyms(sym).flatMap { dResult =>
              acc.updated(ddef, dResult)
            }
          }
        }
        case Apply(fun, args) => {
          val argResults : List[Value[ProcResult]] = args.map(procTerm(_, knownSyms))
          val argReferencedSymbols = argResults.foldLeft(Value(Set.empty[Symbol])) { (acc, argResult) =>
            acc.flatMap { accVal =>
              argResult.flatMap(argResult => argResult.referencedSymbols.map(refs => accVal ++ refs))
            }
          }
          procTerm(fun, knownSyms).flatMap { fnResult =>
            fnResult.inferredInfo.flatMap {
              case InferredInfo.Inlineable(knownParams, List(lastUnknownParams), body) => {
                val finalParams : List[(ValDef,Value[ProcResult],Value[ProcResult])] = (knownParams ++ (lastUnknownParams zip argResults).map {
                  case ((vd,inFn),argV) => (vd,inFn,argV)
                })
                for {
                  inFns <- Value.lifted(finalParams.map(pair => pair._2.map(_.inferredInfo)))
                  nextVs <- Value.lifted(finalParams.map(triple => triple._3.flatMap(_.inferredInfo)))
                  newBody <- (inFns zip nextVs).foldLeft(body) { (acc, pair) =>
                    acc.updated(pair._1, pair._2)
                  }
                } yield mkResult(new {
                    val referencedSymbols = fnResult.referencedSymbols.flatMap { fnSyms =>
                      argReferencedSymbols.map(argSyms => fnSyms ++ argSyms)
                    }
                    val inferredInfo = newBody.inferredInfo
                    val term =
                      for {
                        bodyTerm <- newBody.term
                        vVals <- Value.lifted(finalParams.map(triple => triple._3.flatMap(_.term)))
                      } yield Block(
                        (finalParams.map(_._1) zip vVals).map {
                          case (d @ ValDef(name, tpt, None), v) =>
                            ValDef.copy(d)(name, tpt, Some(v))
                        },
                        bodyTerm)
                    val definitions = newBody.definitions
                  })
              }
              case info =>
                Value {
                  mkResult(new {
                    val referencedSymbols = fnResult.referencedSymbols.flatMap { fnSyms =>
                      argReferencedSymbols.map(argSyms => fnSyms ++ argSyms)
                    }
                    val inferredInfo = Value(info match {
                      case InferredInfo.Inlineable(knownParams, List(lastUnknownParams), body) =>
                        ???
                      case InferredInfo.Inlineable(knownParams, outerUnknownParams :: otherUnknownParams, body) =>
                        InferredInfo.Inlineable(
                          knownParams=knownParams ++ (outerUnknownParams zip argResults).map {
                            case (a, b) => a++Tuple1(b)
                          },
                          unknownParams=otherUnknownParams,
                          body=body)
                      case _ => InferredInfo.Opaque
                    })
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
                  })
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
                    mkResult(new {
                      val referencedSymbols = baseResult.referencedSymbols
                      val inferredInfo = Value(InferredInfo.Opaque)
                      val term = baseResult.term.map { baseTerm =>
                        Select(baseTerm, sym)
                      }
                      val definitions = baseResult.definitions
                    })
                  }
                case _ : NoMatchingImplicits =>
                  if( sym.isDefDef ) {
                    val tree = sym.tree.asInstanceOf[DefDef]
                    for {
                      pair  <- procDefDef(tree, knownSyms)
                      dd <- pair._2
                    } yield pair._1.copy(
                      definitions=pair._1.definitions.map(defs => defs :+ dd)
                    )
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
              error("TODO follow ident sym", term.pos)
              ???
            }
          }
        case Typed(expr, tpt) =>
          procTerm(expr, knownSyms).map { procResult =>
            procResult.copy(term=procResult.term.map { term =>
              Typed(term, tpt)
            })
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

