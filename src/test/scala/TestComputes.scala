package towers.computes.test

import towers.computes._

object TestComputes extends App {

  Predef.assert(doAdd1(2) == 3)

  Predef.assert(doAdd2(2) == 4)

  Predef.assert(doCountdown(5))

  Predef.assert(doAdd1AddedL(2) == 5)
  Predef.assert(doAdd1AddedR(2) == 5)

  println(doUnimapAdd1(List(1,2,3,4)))

  //println(doUnimap2Add1(List(1,2,3,4)))
}

