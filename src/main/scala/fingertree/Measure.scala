package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

trait Measured[T, M] {
  def measure()(implicit m: Measure[T, M]): M
}

trait Measure[T, M] {
  def zero: M

  def apply(c: T): M

  def apply(a: M, b: M): M

  final def apply(a: M, b: M, c: M): M =
    this(this(a, b), c)

  final def apply(a: M, b: M, c: M, d: M): M =
    this(this(this(a, b), c), d)

  final def apply(a: Measured[T, M], b: Measured[T, M]): M =
    this(a.measure()(this), b.measure()(this))

  final def apply(a: Measured[T, M], b: Measured[T, M], c: Measured[T, M]): M =
    this(this(a, b), c.measure()(this))

  final def apply(
      a: Measured[T, M],
      b: Measured[T, M],
      c: Measured[T, M],
      d: Measured[T, M]
  ): M =
    this(this(this(a, b), c.measure()(this)), d.measure()(this))

  final def isAssociative: Boolean =
    forall((x: M, y: M, z: M) => this(this(x, y), z) == this(x, this(y, z)))

  final def zeroIsNeutral: Boolean =
    forall((x: M) => this(zero, x) == x && this(x, zero) == x)

  final def isValid: Boolean =
    zeroIsNeutral && isAssociative
}
