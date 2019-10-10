package towers.test

import org.junit.Assert
import org.junit.Test

import towers._

class TestLambdas {

  inline def m_testReturn1 : Int = ${ Computes.compile(test.return1) }
  @Test
  def testReturn1 = {
    Assert.assertEquals(1, m_testReturn1)
  }

  inline def m_testAdd1 : Tuple1[Int]=>Int = ${ Computes.compileFn(test.add1) }
  @Test
  def testAdd1 = {
    Assert.assertEquals(2, m_testAdd1(Tuple1(1)))
  }

  inline def m_testMapAdd1 : Tuple1[List[Int]]=>List[Int] = ${ Computes.compileFn(test.mapAdd1) }
  @Test
  def testMapAdd1 = {
    Assert.assertEquals(List(2,3,4,5), m_testMapAdd1(Tuple1(List(1,2,3,4))))
  }
}

