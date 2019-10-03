package towers.test

import scala.quoted._

import towers._
import Computes._


val return1 : Computes[Int] = ref { 1 }

val add1 : Computes[Tuple1[Int]==>Int] = ref { fun {
  (i : Computes[Int]) => expr(Tuple1(i), (i : Expr[Int]) => '{ $i + 1 })
} }

def map[S : Type, T : Type : Liftable](list : Computes[List[S]], fn : Computes[Tuple1[S]==>T]) : Computes[List[T]] = {
  lazy val impl : Computes[Tuple1[List[S]]==>List[T]] = ref { fun {
    (list : Computes[List[S]]) =>
      expr(Tuple1(list), (list : Expr[List[S]]) => '{ ${ list }.isEmpty }).branch(
        t=const[List[T]](Nil),
        f=let(expr(Tuple1(list), (list : Expr[List[S]]) => '{ ${ list }.head }), { head =>
          let(expr(Tuple1(list), (list : Expr[List[S]]) => '{ ${ list }.tail }), { tail =>
            expr((fn(Tuple1(head)), impl(Tuple1(tail))), (hd : Expr[T], tl : Expr[List[T]]) => '{ ${ hd } :: ${ tl } })
          })
        }))
  } }
  impl(Tuple1(list))
}

