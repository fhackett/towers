package towers.test

import org.junit.Assert
import org.junit.Test

import towers._

class TestSimple extends Parsers {
  type Elem = Char
  //type Input = Seq[Elem]
  
  /*given [P <: LiteralParser[_]] as Reducer[P,Input=>ParseResult[Char]] {
    inline def apply(p : =>P) : Input=>ParseResult[Char] =
      ???
  }*/


  @Test
  def testSimple : Unit = {
    val p = for {
      a <- literal('a')
      b <- literal('b')
    } yield (a, b)
    println(s"${p(Seq('a', 'b'))}")
    println("test")
  }
}

