package towers.test

import org.junit.Assert
import org.junit.Test

import towers._

class TestLazyTree {
  import LazyTree._

  @Test
  def testConstant = {
    Assert.assertEquals(1, Value(1).result)
  }

  @Test
  def testReplacement = {
    val v = Value(1)
    Assert.assertEquals(2, v.updated(v, 2).result)
  }

  @Test
  def testSimpleDeps = {
    val v = Value(1)
    Assert.assertEquals(4, (for {
      a <- v
      b <- v
    } yield a+b).updated(v, 2).result)
  }

  @Test
  def testSimpleDepsChange = {
    val v = Value(1)
    val expr = for {
      a <- v
      b <- v
    } yield a+b
    Assert.assertEquals(4, expr.flatMap(_ => expr.updated(v, 2)).result)
  }

  @Test
  def testLevel2DepsChange = {
    val v = Value(1)
    val v2 = for {
      a <- v
      b <- v
    } yield a+b
    val expr = for {
      a <- v2
      b <- v2
    } yield a+b
    
    Assert.assertEquals(20, expr.flatMap { x =>
      expr.updated(v, x+1)
    }.result)

    Assert.assertEquals(10, expr.flatMap { x =>
      expr.updated(v2, x+1)
    }.result)
    // check that v is still 1 even though we overrode v2
    Assert.assertEquals(11, expr.flatMap { x =>
      expr.updated(v2, x+1).flatMap { x2 =>
        v.map(vv => x2 + vv)
      }
    }.result)
  }

  @Test
  def testRecallOriginalValue = {
    val v = Value(1)
    // referencing v again outside the updated context should still return 1
    Assert.assertEquals(3, v.updated(v, 2).flatMap(a => v.map(b => a+b)).result)
  }
}

