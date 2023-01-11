package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

trait Measure[T, M] {
  def zero: M

  def apply(c: T): M

  def apply(a: M, b: M): M

  final def apply(a: M, b: M, c: M): M =
    this(this(a, b), c)

  final def apply(a: M, b: M, c: M, d: M): M =
    this(this(this(a, b), c), d)

  final def isAssociative: Boolean =
    forall((x: M, y: M, z: M) => this(this(x, y), z) == this(x, this(y, z)))

  final def zeroIsNeutral: Boolean =
    forall((x: M) => this(zero, x) == x && this(x, zero) == x)

  final def isValid: Boolean =
    zeroIsNeutral && isAssociative
}
