package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

trait Measure[T, M] {
  def zero: M

  def apply(c: T): M

  def |+|(a: M, b: M): M

  final def |+|(elems: List[M]): M = elems.foldLeft(zero)(|+|)

  final def isAssociative: Boolean =
    forall((x: M, y: M, z: M) => |+|(|+|(x, y), z) == |+|(x, |+|(y, z)))

  final def zeroIsNeutral: Boolean =
    forall((x: M) => |+|(zero, x) == x && |+|(x, zero) == x)

  final def isValid: Boolean =
    zeroIsNeutral && isAssociative
}
