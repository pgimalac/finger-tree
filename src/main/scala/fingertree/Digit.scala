package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

/// This file defines the data structure for the digits in a finger tree, which
/// represent a special case at the top level of the 2-3 trees (Nodes[T]) composing
/// a finger tree. These top levels can optionally have 1 or 4 children, which we'll
/// call segments, to make operations on the finger tree simpler. The case classes
/// of Digit[T] are found at the end of the file.

private sealed trait Digit[T, M] extends Measured[T, M]:

  /// ***INVARIANT AND PROOF HELPER FUNCTIONS*** ///

  /// Applies a predicate to each segment of the digit
  def forall(p: Node[T, M] => Boolean): Boolean = {
    this match
      case Digit1(a)             => p(a)
      case Digit2(a, b, _)       => p(a) && p(b)
      case Digit3(a, b, c, _)    => p(a) && p(b) && p(c)
      case Digit4(a, b, c, d, _) => p(a) && p(b) && p(c) && p(d)
  }

  /// Checks the invariant that segment of the digit is a fully-balanced tree
  /// of the given depth
  def isWellFormed(depth: BigInt)(implicit m: Measure[T, M]): Boolean = {
    require(depth >= 0 && m.isValid)

    this.forall(_.isWellFormed(depth))
  }

  /// ***CONVERSION AND HELPER FUNCTIONS*** ///

  /// Gets first segment in a digit
  def headL(depth: BigInt)(implicit m: Measure[T, M]): Node[T, M] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(a)             => a
      case Digit2(a, _, _)       => a
      case Digit3(a, _, _, _)    => a
      case Digit4(a, _, _, _, _) => a
    }
  }.ensuring(res => res.isWellFormed(depth))

  /// Gets last segment in a digit
  def headR(depth: BigInt)(implicit m: Measure[T, M]): Node[T, M] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(a)             => a
      case Digit2(_, b, _)       => b
      case Digit3(_, _, c, _)    => c
      case Digit4(_, _, _, d, _) => d
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res == this.toNodeList(depth).last
  )

  /// Produces a new digit with all the segments of the original except for the first
  def tailL(depth: BigInt)(implicit m: Measure[T, M]): Option[Digit[T, M]] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(_)       => None()
      case Digit2(_, b, _) => Some(Digit1(b))
      case Digit3(_, b, c, _) =>
        Some(Digit2(b, c, m(b, c)))
      case Digit4(_, b, c, d, _) =>
        Some(Digit3(b, c, d, m(b, c, d)))
    }
  }.ensuring(res => res.forall(_.isWellFormed(depth)))

  /// Produces a new digit with all the segments of the original except for the last
  def tailR(depth: BigInt)(implicit m: Measure[T, M]): Option[Digit[T, M]] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(_)       => None()
      case Digit2(a, _, _) => Some(Digit1(a))
      case Digit3(a, b, _, _) =>
        Some(Digit2(a, b, m(a, b)))
      case Digit4(a, b, c, _, _) =>
        Some(Digit3(a, b, c, m(a, b, c)))
    }
  }.ensuring(res => res.forall(_.isWellFormed(depth)))

  /// Converts a digit to a list of Node[T]'s, for easier proof ergonomics
  def toNodeList(depth: BigInt)(implicit m: Measure[T, M]): List[Node[T, M]] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))
    decreases(this)

    this.tailL(depth) match {
      case None() => List(this.headL(depth))
      case Some(tail) => {
        FingerTreeLemmas.headTailConcatL(this, depth)

        Cons(this.headL(depth), tail.toNodeList(depth))
      }
    }
  }.ensuring(res =>
    !res.isEmpty
      && res.forall(_.isWellFormed(depth))
      && res == (this match {
        case Digit1(a)             => List[Node[T, M]](a)
        case Digit2(a, b, _)       => List[Node[T, M]](a, b)
        case Digit3(a, b, c, _)    => List[Node[T, M]](a, b, c)
        case Digit4(a, b, c, d, _) => List[Node[T, M]](a, b, c, d)
      })
      && Helpers.toListL(res, depth) == this.toListL(depth)
      && Helpers.toListR(res, depth) == this.toListR(depth)
  )

  /// Constructs a list from a node, according to an in-order traversal
  def toListL(depth: BigInt)(implicit m: Measure[T, M]): List[T] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(a) => a.toListL(depth)
      case Digit2(a, b, _) => {
        ListLemmas.reverseConcat(a.toListL(depth), b.toListL(depth))

        a.toListL(depth) ++ b.toListL(depth)
      }
      case Digit3(a, b, c, _) => {
        ListLemmas.reverseConcat(a.toListL(depth), b.toListL(depth))
        ListLemmas.reverseConcat(
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.associativeConcat(
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )

        a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth)
      }
      case Digit4(a, b, c, d, _) => {
        ListLemmas.reverseConcat(a.toListL(depth), b.toListL(depth))
        ListLemmas.reverseConcat(
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.reverseConcat(
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth)
        )
        ListLemmas.associativeConcat(
          d.toListR(depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )

        a.toListL(depth) ++ b.toListL(depth)
          ++ c.toListL(depth) ++ d.toListL(depth)
      }
    }
  }.ensuring(res =>
    !res.isEmpty
      && res.reverse == this.toListR(depth)
  )

  /// Constructs a list from a node, according to a reversed in-order traversal
  def toListR(depth: BigInt)(implicit m: Measure[T, M]): List[T] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(a)       => a.toListR(depth)
      case Digit2(a, b, _) => b.toListR(depth) ++ a.toListR(depth)
      case Digit3(a, b, c, _) =>
        c.toListR(depth) ++ b.toListR(depth) ++ a.toListR(depth)
      case Digit4(a, b, c, d, _) =>
        d.toListR(depth) ++ c.toListR(depth)
          ++ b.toListR(depth) ++ a.toListR(depth)
    }
  }.ensuring(!_.isEmpty)

  /// Constructs a simple one-level finger tree from a digit
  def toTree(depth: BigInt)(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(a)             => Single(a)
      case Digit2(a, b, measure) => Deep(Digit1(a), Empty(), Digit1(b), measure)
      case Digit3(a, b, c, measure) => {
        ListLemmas.associativeConcat(
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )

        val newPrefix = Digit2(a, b, m(a, b))
        Deep(newPrefix, Empty(), Digit1(c), measure)
      }
      case Digit4(a, b, c, d, measure) => {
        ListLemmas.associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth),
          d.toListL(depth)
        )
        ListLemmas.associativeConcat(
          d.toListR(depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )

        Deep(
          Digit2(a, b, m(a, b)),
          Empty(),
          Digit2(c, d, m(c, d)),
          measure
        )
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && !res.isEmpty(depth)
      && res.toListL(depth) == this.toListL(depth)
      && res.toListR(depth) == this.toListR(depth)
  )

  def measure()(implicit m: Measure[T, M]): M = {
    require(m.isValid)

    this match {
      case Digit1(a)                   => a.measure()
      case Digit2(_, _, measure)       => measure
      case Digit3(_, _, _, measure)    => measure
      case Digit4(_, _, _, _, measure) => measure
    }
  }

/// A Digit[T] is either a:
/// - Digit1[T](Node[T]),
/// - Digit2[T](Node[T], Node[T]),
/// - Digit3[T](Node[T], Node[T], Node[T]), or
/// - Digit4[T](Node[T], Node[T], Node[T], Node[T])

private final case class Digit1[T, M](
    a: Node[T, M]
) extends Digit[T, M]
private final case class Digit2[T, M](
    a: Node[T, M],
    b: Node[T, M],
    m: M
) extends Digit[T, M]
private final case class Digit3[T, M](
    a: Node[T, M],
    b: Node[T, M],
    c: Node[T, M],
    m: M
) extends Digit[T, M]
private final case class Digit4[T, M](
    a: Node[T, M],
    b: Node[T, M],
    c: Node[T, M],
    d: Node[T, M],
    m: M
) extends Digit[T, M]
