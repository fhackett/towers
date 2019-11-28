package towers.test

import org.junit.Assert
import org.junit.Test

import towers._

class TestSimple {
  import Compiler.given

  @Test
  def test1 = {
    Assert.assertEquals(1, Compiler.compile(1))
  }

  /*
  // not fixed by -Yretain-trees
  @Test
  def testReturn1Inner = {
    Assert.assertEquals(1, Compiler.compile {
      def return1 : Int = 1
      return1
    })
  }
  */

  def return1 = 1

  @Test
  def testReturn1 = {
    Assert.assertEquals(1, Compiler.compile(return1))
  }

  @Test
  def test1Plus1 = {
    Assert.assertEquals(2, Compiler.compile(1+1))
  }


  def add1(x : Int) = x+1

  @Test
  def testAdd1 = {
    Assert.assertEquals(2, Compiler.compile(add1(1)))
  }

  /*
  @Test
  def testAdd1Fn = {
    Assert.assertEquals(2, Compiler.compile[Int=>Int](add1)(1))
  }*/

  /*
  def listMap(lst : List[Int], fn : Int=>Int) : List[Int] =
    lst match {
      case Nil => Nil
      case hd :: tl => fn(hd) :: listMap(tl, fn)
    }

  @Test
  def testListMapIdentity = {
    Assert.assertEquals(List(1,2,3,4), Compiler.compile(listMap(List(1,2,3,4), identity)))
  }

  @Test
  def testListMapAdd1 = {
    Assert.assertEquals(List(2,3,4,5), Compiler.compile(listMap(List(1,2,3,4), _+1)))
  }*/
}

