package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

trait Measure[T, M] {
  def zero: M

  def apply(c: T): M

  def |+|(a: M, b: M): M

  final def |+|(elems: List[M]): M = elems.foldLeft(zero)(|+|)
}
