package test.towers.computes

import towers.computes._

object ComputesTest extends App {

  Predef.assert(doAdd1(2) == 3)

  Predef.assert(doCountdown(5))

  Predef.assert(doUnimapAdd1(List(1,2,3,4)) == List(2,3,4,5))
}

