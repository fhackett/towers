package towers.grammar.test

import towers.grammar.Test

object TestGrammar extends App {

  Predef.assert(Test.matchEOF("") == Some(()))
  Predef.assert(Test.matchEOF("A") == None)

  Predef.assert(Test.matchAs("") == Some(Seq.empty))
  //Predef.assert(Test.matchAs("a") == Some(Seq('a')))
  //Predef.assert(Test.matchAs("aaaa") == Some(Seq('a', 'a', 'a', 'a')))
  //Predef.assert(Test.matchAs(" aaaa") == Some(Seq.empty))

}

