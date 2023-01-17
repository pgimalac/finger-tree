package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

/// This file contains various helper functions which didn't fit directly
/// with the definition of the types

object Helpers {
  import NodeHelpers._
  import TreeHelpers._

  /// Converts a list of Nodes to a list of elements, from the left side
  def toListL[T, M](elems: List[Node[T, M]], depth: BigInt)(implicit
      m: Measure[T, M]
  ): List[T] = {
    require(
      depth >= 0
        && m.isValid
        && elems.forall(_.isWellFormed(depth))
    )

    elems match {
      case Cons(head, tail) =>
        ListLemmas.reverseConcat(head.toListL(depth), toListL(tail, depth))
        head.toListL(depth) ++ toListL(tail, depth)
      case Nil() => Nil()
    }
  }.ensuring(res => res.reverse == toListR(elems, depth))

  /// Converts a list of Nodes to a list of elements, from the right side
  def toListR[T, M](elems: List[Node[T, M]], depth: BigInt)(implicit
      m: Measure[T, M]
  ): List[T] = {
    require(
      depth >= 0
        && m.isValid
        && elems.forall(_.isWellFormed(depth))
    )

    elems match {
      case Cons(head, tail) => toListR(tail, depth) ++ head.toListR(depth)
      case Nil()            => Nil()
    }
  }

  /// Groups a List of Node to a single level deeper
  def toNodes[T, M](elems: List[Node[T, M]], depth: BigInt)(implicit
      m: Measure[T, M]
  ): List[Node[T, M]] = {
    decreases(elems.size)
    require(
      depth >= 0
        && elems.size >= 2
        && m.isValid
        && elems.forall(_.isWellFormed(depth))
    )

    elems match {
      case Nil()          => ???
      case Cons(a, Nil()) => ???
      case Cons(a, Cons(b, Nil())) =>
        List(makeNode(a, b, depth))
      case Cons(a, Cons(b, Cons(c, Nil()))) =>
        check(Cons(b, Cons(c, Nil())).forall(_.isWellFormed(depth)))
        ListLemmas.associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth)
        )
        List[Node[T, M]](makeNode(a, b, c, depth))
      case Cons(a, Cons(b, Cons(c, Cons(d, Nil())))) =>
        check(Cons(c, Cons(d, Nil())).forall(_.isWellFormed(depth)))
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
        check(
          toListL(Cons(c, Cons(d, Nil())), depth) ==
            c.toListL(depth) ++ d.toListL(depth) ++ Nil()
        )
        check(
          toListR(Cons(c, Cons(d, Nil())), depth) ==
            Nil() ++ d.toListR(depth) ++ c.toListR(depth)
        )
        List[Node[T, M]](makeNode(a, b, depth), makeNode(c, d, depth))
      case Cons(a, Cons(b, Cons(c, tail))) => {
        check(Cons(c, tail).forall(_.isWellFormed(depth)))
        ListLemmas.associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth),
          toListL(tail, depth)
        )
        ListLemmas.associativeConcat(
          toListR(tail, depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        Cons(makeNode(a, b, c, depth), toNodes(tail, depth))
      }
    }
  }.ensuring(res =>
    res.forall(_.isWellFormed(depth + 1))
      && toListL(res, depth + 1) == toListL(elems, depth)
      && toListR(res, depth + 1) == toListR(elems, depth)
  )

  /// Builds a FingerTree from an optional prefix, a spine and a suffix
  def deepL[T, M](
      prefixTail: Option[Digit[T, M]],
      spine: FingerTree[T, M],
      suffix: Digit[T, M],
      depth: BigInt
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(
      depth >= 0
        && m.isValid
        && spine.isWellFormed(depth + 1)
        && prefixTail.forall(_.isWellFormed(depth))
        && suffix.isWellFormed(depth)
    )

    prefixTail match {
      case Some(digit) => makeDeep(digit, spine, suffix, depth)
      case None() =>
        spine match {
          case Empty() => suffix.toTree(depth)
          case Single(value) =>
            makeDeep(value.toDigit(depth + 1), Empty(), suffix, depth)
          case Deep(spinePrefix, spineSpine, spineSuffix, _) =>
            val prefix = spinePrefix.tailL(depth + 1) match {
              case Some(pref) => pref.toListL(depth + 1)
              case None()     => List()
            }
            FingerTreeLemmas.headTailConcatL(spinePrefix, depth + 1)
            ListLemmas.associativeConcat(
              spinePrefix.headL(depth + 1).toListL(depth + 1),
              prefix,
              spineSpine.toListL(depth + 2),
              spineSuffix.toListL(depth + 1)
            )

            val newPrefix = spinePrefix.headL(depth + 1).toDigit(depth + 1)
            val newSpine = deepL(
              spinePrefix.tailL(depth + 1),
              spineSpine,
              spineSuffix,
              depth + 1
            )
            makeDeep(newPrefix, newSpine, suffix, depth)
        }
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && {
        val prefix = prefixTail match {
          case Some(pref) => pref.toListL(depth)
          case None()     => List()
        }
        res.toListL(depth) ==
          prefix ++ spine.toListL(depth + 1) ++ suffix.toListL(depth)
      }
  )

  /// Builds a FingerTree from a prefix, a spine and an optional suffix
  def deepR[T, M](
      prefix: Digit[T, M],
      spine: FingerTree[T, M],
      suffixTail: Option[Digit[T, M]],
      depth: BigInt
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(
      depth >= 0
        && m.isValid
        && spine.isWellFormed(depth + 1)
        && prefix.isWellFormed(depth)
        && suffixTail.forall(_.isWellFormed(depth))
    )

    suffixTail match {
      case Some(digit) =>
        makeDeep(prefix, spine, digit, depth)
      case None() =>
        spine match {
          case Empty() => prefix.toTree(depth)
          case Single(value) =>
            makeDeep(prefix, Empty(), value.toDigit(depth + 1), depth)
          case Deep(spinePrefix, spineSpine, spineSuffix, _) =>
            val suffix = spineSuffix.tailR(depth + 1) match {
              case Some(suff) => suff.toListR(depth + 1)
              case None()     => List()
            }
            FingerTreeLemmas.headTailConcatR(spineSuffix, depth + 1)
            ListLemmas.associativeConcat(
              spineSuffix.headR(depth + 1).toListR(depth + 1),
              suffix,
              spineSpine.toListR(depth + 2),
              spinePrefix.toListR(depth + 1)
            )

            val newSpine = deepR(
              spinePrefix,
              spineSpine,
              spineSuffix.tailR(depth + 1),
              depth + 1
            )
            val newSuffix = spineSuffix.headR(depth + 1).toDigit(depth + 1)
            makeDeep(prefix, newSpine, newSuffix, depth)
        }
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && {
        val suffix = suffixTail match {
          case Some(suff) => suff.toListR(depth)
          case None()     => List()
        }
        res.toListR(depth) ==
          suffix ++ spine.toListR(depth + 1) ++ prefix.toListR(depth)
      }
  )

}
