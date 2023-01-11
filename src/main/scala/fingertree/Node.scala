package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

/// This file defines the data structure for the nodes in a finger tree, which
/// represent fully-balanced 2-3 trees of a given depth, maintaining the invariant
/// for finger trees that the original polymorphically recursive type would have.
/// The case classes of Node[T] are found at the end of the file.

sealed trait Node[T, M]:

  /// ***INVARIANT FUNCTIONS*** ///

  /// Checks the invariant that the node is a fully-balanced tree of the given depth
  def isWellFormed(depth: BigInt)(implicit m: Measure[T, M]): Boolean = {
    require(depth >= 0 && m.isValid)

    this match {
      case Leaf(a) => depth == 0
      case Node2(left, right, measure) =>
        depth != 0 &&
        left.isWellFormed(depth - 1) &&
        right.isWellFormed(depth - 1) &&
        measure == m(left.measure(), right.measure())
      case Node3(left, middle, right, measure) =>
        depth != 0 &&
        left.isWellFormed(depth - 1) &&
        middle.isWellFormed(depth - 1) &&
        right.isWellFormed(depth - 1) &&
        measure == m(left.measure(), middle.measure(), right.measure())
    }
  }

  /// ***CONVERSION FUNCTIONS*** ///

  /// Constructs a list from a node, according to an in-order traversal
  def toListL(depth: BigInt)(implicit m: Measure[T, M]): List[T] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Leaf(a) => List(a)
      case Node2(left, right, _) => {
        ListLemmas.reverseConcat(
          left.toListL(depth - 1),
          right.toListL(depth - 1)
        )

        left.toListL(depth - 1) ++ right.toListL(depth - 1)
      }
      case Node3(left, middle, right, _) => {
        ListLemmas.reverseConcat(
          left.toListL(depth - 1),
          middle.toListL(depth - 1)
        )
        ListLemmas.reverseConcat(
          left.toListL(depth - 1) ++ middle.toListL(depth - 1),
          right.toListL(depth - 1)
        )
        ListLemmas.associativeConcat(
          right.toListR(depth - 1),
          middle.toListR(depth - 1),
          left.toListR(depth - 1)
        )

        left.toListL(depth - 1) ++ middle.toListL(depth - 1)
          ++ right.toListL(depth - 1)
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
      case Leaf(a) => List(a)
      case Node2(left, right, _) =>
        right.toListR(depth - 1) ++ left.toListR(depth - 1)
      case Node3(left, middle, right, _) =>
        right.toListR(depth - 1) ++ middle.toListR(depth - 1)
          ++ left.toListR(depth - 1)
    }
  }.ensuring(!_.isEmpty)

  /// Constructs a digit from a node, using each branch as an element in the digit
  def toDigit(depth: BigInt)(implicit m: Measure[T, M]): Digit[T, M] = {
    require(depth >= 1 && m.isValid && this.isWellFormed(depth))

    this match {
      case Leaf(_)                     => ??? // Should never get here
      case Node2(left, right, measure) => Digit2(left, right, measure)
      case Node3(left, middle, right, measure) =>
        Digit3(left, middle, right, measure)
    }
  }.ensuring(res =>
    res.isWellFormed(depth - 1) &&
      res.toListL(depth - 1) == this.toListL(depth) &&
      res.toListR(depth - 1) == this.toListR(depth)
  )

  def measure()(implicit m: Measure[T, M]): M = {
    require(m.isValid)

    this match {
      case Leaf(a)                 => m(a)
      case Node2(_, _, measure)    => measure
      case Node3(_, _, _, measure) => measure
    }
  }

/// A Node[T] is either a:
/// - Leaf[T](T)
/// - Node2[T](Node[T], Node[T]), or
/// - Node3[T](Node[T], Node[T], Node[T])
final case class Leaf[T, M](a: T) extends Node[T, M]
final case class Node2[T, M](
    left: Node[T, M],
    right: Node[T, M],
    m: M
) extends Node[T, M]
final case class Node3[T, M](
    left: Node[T, M],
    middle: Node[T, M],
    right: Node[T, M],
    m: M
) extends Node[T, M]
