package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

/// This file defines the data structure for the digits in a finger tree, which
/// represent a special case at the top level of the 2-3 trees (Nodes[T]) composing
/// a finger tree. These top levels can optionally have 1 or 4 children, which we'll
/// call segments, to make operations on the finger tree simpler. The case classes
/// of Digit[T] are found at the end of the file.

sealed trait Digit[T, M]:
  import DigitHelpers._

  /// ***INVARIANT AND PROOF HELPER FUNCTIONS*** ///

  /// Checks the invariant that segment of the digit is a fully-balanced tree
  /// of the given depth
  def isWellFormed(depth: BigInt)(implicit m: Measure[T, M]): Boolean = {
    require(depth >= 0 && m.isValid)

    this match {
      case Digit1(a) => a.isWellFormed(depth)
      case Digit2(a, b, measure) =>
        a.isWellFormed(depth) && b.isWellFormed(depth) &&
        measure == m(a.measure(), b.measure())
      case Digit3(a, b, c, measure) =>
        a.isWellFormed(depth) && b.isWellFormed(depth) &&
        c.isWellFormed(depth) &&
        measure == m(a.measure(), b.measure(), c.measure())
      case Digit4(a, b, c, d, measure) =>
        a.isWellFormed(depth) && b.isWellFormed(depth) &&
        c.isWellFormed(depth) && d.isWellFormed(depth) &&
        measure == m(a.measure(), b.measure(), c.measure(), d.measure())
    }
  }

  /// ***CONVERSION AND HELPER FUNCTIONS*** ///

  /// Gets first segment in a digit
  def headL(depth: BigInt)(implicit m: Measure[T, M]): Node[T, M] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(a) => a
      case Digit2(a, b, _) =>
        ListLemmas.headConcat(a.toListL(depth), b.toListL(depth))
        ListLemmas.lastConcat(b.toListR(depth), a.toListR(depth))

        a
      case Digit3(a, b, c, _) =>
        ListLemmas.headConcat(a.toListL(depth), b.toListL(depth))
        ListLemmas.lastConcat(b.toListR(depth), a.toListR(depth))
        ListLemmas.headConcat(
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.lastConcat(
          c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth)
        )

        a
      case Digit4(a, b, c, d, _) =>
        ListLemmas.headConcat(a.toListL(depth), b.toListL(depth))
        ListLemmas.lastConcat(b.toListR(depth), a.toListR(depth))
        ListLemmas.headConcat(
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.lastConcat(
          c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth)
        )
        ListLemmas.headConcat(
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth)
        )
        ListLemmas.lastConcat(
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth)
        )

        a
    }
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      this.toListL(depth).headOption == res.toListL(depth).headOption &&
      this.toListR(depth).lastOption == res.toListR(depth).lastOption
  )

  /// Gets last segment in a digit
  def headR(depth: BigInt)(implicit m: Measure[T, M]): Node[T, M] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(a) => a
      case Digit2(a, b, _) =>
        ListLemmas.lastConcat(a.toListL(depth), b.toListL(depth))
        ListLemmas.headConcat(b.toListR(depth), a.toListR(depth))

        b
      case Digit3(a, b, c, _) =>
        ListLemmas.lastConcat(a.toListL(depth), b.toListL(depth))
        ListLemmas.headConcat(b.toListR(depth), a.toListR(depth))
        ListLemmas.lastConcat(
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.headConcat(
          c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth)
        )

        c
      case Digit4(a, b, c, d, _) =>
        ListLemmas.lastConcat(a.toListL(depth), b.toListL(depth))
        ListLemmas.headConcat(b.toListR(depth), a.toListR(depth))
        ListLemmas.lastConcat(
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.headConcat(
          c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth)
        )
        ListLemmas.lastConcat(
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth)
        )
        ListLemmas.headConcat(
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth)
        )

        d
    }
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res == this.toNodeList(depth).last &&
      this.toListR(depth).headOption == res.toListR(depth).headOption &&
      this.toListL(depth).lastOption == res.toListL(depth).lastOption
  )

  /// Produces a new digit with all the segments of the original except for the first
  def tailL(depth: BigInt)(implicit m: Measure[T, M]): Option[Digit[T, M]] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(_)             => None()
      case Digit2(_, b, _)       => Some(makeDigit(b, depth))
      case Digit3(_, b, c, _)    => Some(makeDigit(b, c, depth))
      case Digit4(_, b, c, d, _) => Some(makeDigit(b, c, d, depth))
    }
  }.ensuring(res => res.forall(_.isWellFormed(depth)))

  /// Produces a new digit with all the segments of the original except for the last
  def tailR(depth: BigInt)(implicit m: Measure[T, M]): Option[Digit[T, M]] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Digit1(_)             => None()
      case Digit2(a, _, _)       => Some(makeDigit(a, depth))
      case Digit3(a, b, _, _)    => Some(makeDigit(a, b, depth))
      case Digit4(a, b, c, _, _) => Some(makeDigit(a, b, c, depth))
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
    !res.isEmpty &&
      res.forall(_.isWellFormed(depth)) &&
      res == (this match {
        case Digit1(a)             => List[Node[T, M]](a)
        case Digit2(a, b, _)       => List[Node[T, M]](a, b)
        case Digit3(a, b, c, _)    => List[Node[T, M]](a, b, c)
        case Digit4(a, b, c, d, _) => List[Node[T, M]](a, b, c, d)
      }) &&
      Helpers.toListL(res, depth) == this.toListL(depth) &&
      Helpers.toListR(res, depth) == this.toListR(depth)
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
    !res.isEmpty &&
      res.reverse == this.toListR(depth)
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
      case Digit1(a) => Single(a)
      case Digit2(a, b, measure) =>
        Deep(makeDigit(a, depth), Empty(), makeDigit(b, depth), measure)
      case Digit3(a, b, c, measure) => {
        ListLemmas.associativeConcat(
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )

        Deep(makeDigit(a, b, depth), Empty(), makeDigit(c, depth), measure)
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

        Deep(makeDigit(a, b, depth), Empty(), makeDigit(c, d, depth), measure)
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      !res.isEmpty(depth) &&
      res.toListL(depth) == this.toListL(depth) &&
      res.toListR(depth) == this.toListR(depth)
  )

  /// *** MEASURE *** ///

  def measure()(implicit m: Measure[T, M]): M = {
    require(m.isValid)

    this match {
      case Digit1(a)                   => a.measure()
      case Digit2(_, _, measure)       => measure
      case Digit3(_, _, _, measure)    => measure
      case Digit4(_, _, _, _, measure) => measure
    }
  }

  def split(depth: BigInt, acc: M, p: M => Boolean)(implicit
      m: Measure[T, M]
  ): (Option[Digit[T, M]], Node[T, M], Option[Digit[T, M]]) = {
    decreases(this)
    require(
      depth >= 0 &&
        m.isValid &&
        this.isWellFormed(depth) &&
        !p(acc) && p(this.measure())
    )

    this match {
      case Digit1(a) => (None(), a, None())
      case Digit2(a, b, _) if p(m(acc, a.measure())) =>
        (None(), a, Some(makeDigit(b, depth)))
      case Digit2(a, b, _) =>
        (Some(makeDigit(a, depth)), b, None())
      case Digit3(a, b, c, _) if p(m(acc, a.measure())) =>
        (None(), a, Some(makeDigit(b, c, depth)))
      case Digit3(a, b, c, _) if p(m(acc, a.measure(), b.measure())) =>
        (Some(makeDigit(a, depth)), b, Some(makeDigit(c, depth)))
      case Digit3(a, b, c, _) =>
        (Some(makeDigit(a, b, depth)), c, None())
      case Digit4(a, b, c, d, _) if p(m(acc, a.measure())) =>
        (None(), a, Some(makeDigit(b, c, d, depth)))
      case Digit4(a, b, c, d, _) if p(m(acc, a.measure(), b.measure())) =>
        (Some(makeDigit(a, depth)), b, Some(makeDigit(c, d, depth)))
      case Digit4(a, b, c, d, _)
          if p(m(acc, a.measure(), b.measure(), c.measure())) =>
        (Some(makeDigit(a, b, depth)), c, Some(makeDigit(d, depth)))
      case Digit4(a, b, c, d, _) =>
        (Some(makeDigit(a, b, c, depth)), d, None())
    }
  }.ensuring { case (pref, elem, suff) =>
    pref.forall(_.isWellFormed(depth)) &&
    elem.isWellFormed(depth) &&
    suff.forall(_.isWellFormed(depth)) &&
    p(m(acc, elem.measure())) && {
      val (prefL, prefR) = pref match {
        case None()     => (List(), List())
        case Some(pref) => (pref.toListL(depth), pref.toListR(depth))
      }
      val (suffL, suffR) = suff match {
        case None()     => (List(), List())
        case Some(suff) => (suff.toListL(depth), suff.toListR(depth))
      }
      this.toListL(depth) == prefL ++ elem.toListL(depth) ++ suffL &&
      this.toListR(depth) == suffR ++ elem.toListR(depth) ++ prefR
    }
  }

/// A Digit[T] is either a:
/// - Digit1[T](Node[T]),
/// - Digit2[T](Node[T], Node[T]),
/// - Digit3[T](Node[T], Node[T], Node[T]), or
/// - Digit4[T](Node[T], Node[T], Node[T], Node[T])

final case class Digit1[T, M](
    a: Node[T, M]
) extends Digit[T, M]
final case class Digit2[T, M](
    a: Node[T, M],
    b: Node[T, M],
    m: M
) extends Digit[T, M]
final case class Digit3[T, M](
    a: Node[T, M],
    b: Node[T, M],
    c: Node[T, M],
    m: M
) extends Digit[T, M]
final case class Digit4[T, M](
    a: Node[T, M],
    b: Node[T, M],
    c: Node[T, M],
    d: Node[T, M],
    m: M
) extends Digit[T, M]

object DigitHelpers {
  inline def makeDigit[T, M](a: Node[T, M], depth: BigInt)(implicit
      m: Measure[T, M]
  ): Digit[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        a.isWellFormed(depth)
    )
    Digit1[T, M](a)
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res.toListL(depth) == a.toListL(depth) &&
      res.toListR(depth) == a.toListR(depth)
  )

  inline def makeDigit[T, M](a: Node[T, M], b: Node[T, M], depth: BigInt)(
      implicit m: Measure[T, M]
  ): Digit[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        a.isWellFormed(depth) &&
        b.isWellFormed(depth)
    )
    Digit2[T, M](a, b, m(a.measure(), b.measure()))
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res.toListL(depth) == a.toListL(depth) ++ b.toListL(depth) &&
      res.toListR(depth) == b.toListR(depth) ++ a.toListR(depth)
  )

  inline def makeDigit[T, M](
      a: Node[T, M],
      b: Node[T, M],
      c: Node[T, M],
      depth: BigInt
  )(implicit
      m: Measure[T, M]
  ): Digit[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        a.isWellFormed(depth) &&
        b.isWellFormed(depth) &&
        c.isWellFormed(depth)
    )

    Digit3[T, M](a, b, c, m(a.measure(), b.measure(), c.measure()))
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res.toListL(depth) == a.toListL(depth) ++ b.toListL(depth)
      ++ c.toListR(depth) &&
      res.toListR(depth) == c.toListR(depth) ++ b.toListR(depth)
      ++ a.toListR(depth)
  )

  inline def makeDigit[T, M](
      a: Node[T, M],
      b: Node[T, M],
      c: Node[T, M],
      d: Node[T, M],
      depth: BigInt
  )(implicit
      m: Measure[T, M]
  ): Digit[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        a.isWellFormed(depth) &&
        b.isWellFormed(depth) &&
        c.isWellFormed(depth) &&
        d.isWellFormed(depth)
    )

    Digit4[T, M](
      a,
      b,
      c,
      d,
      m(a.measure(), b.measure(), c.measure(), d.measure())
    )
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res.toListL(depth) == a.toListL(depth) ++ b.toListL(depth)
      ++ c.toListR(depth) ++ d.toListL(depth) &&
      res.toListR(depth) == d.toListR(depth) ++ c.toListR(depth)
      ++ b.toListR(depth) ++ a.toListR(depth)
  )
}
