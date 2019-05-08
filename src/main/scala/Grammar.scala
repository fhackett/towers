package polyparse.grammar

import polyparse.computes.Computes._

type GrammarType[ET,T] = FunctionType[(ET,GrammarType[ET,T]),T]

sealed abstract class Grammar[ET : Type, T : Type] extends Computable[GrammarType[ET,T]]

case class TerminalGrammar[ET : Type](term : Computes[ET]) extends Grammar[ET,ET] {
  def toComputes = function(e => term.let(target => e._1.switch(cases=List((target,target)), default=e._2)))
}
case class DisjunctionGrammar[ET : Type, T : Type](left : Grammar[ET,T], right : Grammar[ET,T]) extends Grammar[ET,T] {
  def toComputes = function(e => left((e._1, function(ee => right((e._1, e._2))))))
}
case class TableGrammar[ET,T](cases : List[(Computes[ET],Grammar[ET,T])]) extends Grammar[ET,T]

// enum for all language terms
// some kind of wrapper ("embed"?) to show where each wrapper goes
// multiple optimmiser passes to get the right structure, last one implicitly hands off to compiler
// add any specialised terms necessary for optimisation to the term language
// TODO: how to deal with inspecting the output language (what to expose: request bounded const folds, case splitting?, fresh vars)

object Grammar {
  def term[T : Liftable : Type](t : T) : Grammar[T,T] =
    function(e =>
        e.switch(cases=List(
          (t, ???)
        ), default=???))

  def choice[ET : Type, T : Type](left : Grammar[ET,T], right : Grammar[ET,T]) : Grammar[ET,T] =


  implicit class GrammarOps[ET : Type, T : Type](lhs : =>Grammar[ET,T]) {
    def flatMap[T2 : Type](fn : Computes[T] => Grammar[ET,T2]) : Grammar[ET,T2] =
      function(e =>
          lhs(e).let(res => ???))
    def map[T2 : Type](fn : Computes[FunctionType[T,T2]]) : Grammar[ET,T2] =
      function(e =>
          lhs(e).let(res => fn(res)))
  }
}

