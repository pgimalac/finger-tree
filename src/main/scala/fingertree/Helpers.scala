package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

/// This file contains various helper functions which didn't fit directly
/// with the definition of the types

object Helpers {
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
        List(Node2(a, b, m(a.measure(), b.measure())))
      case Cons(a, Cons(b, Cons(c, Nil()))) =>
        ListLemmas.associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth)
        )
        List[Node[T, M]](
          Node3(a, b, c, m(a.measure(), b.measure(), c.measure()))
        )
      case Cons(a, Cons(b, Cons(c, Cons(d, Nil())))) =>
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
            c.toListL(depth) ++ d.toListL(depth)
        )
        check(
          toListR(Cons(c, Cons(d, Nil())), depth) ==
            d.toListR(depth) ++ c.toListR(depth)
        )
        List[Node[T, M]](
          Node2(a, b, m(a.measure(), b.measure())),
          Node2(c, d, m(c.measure(), d.measure()))
        )
      case Cons(a, Cons(b, Cons(c, tail))) => {
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
        Cons(
          Node3(a, b, c, m(a.measure(), b.measure(), c.measure())),
          toNodes(tail, depth)
        )
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
      case Some(digit) =>
        Deep(
          digit,
          spine,
          suffix,
          m(digit.measure(), spine.measure(), suffix.measure())
        )
      case None() =>
        spine match {
          case Empty() => suffix.toTree(depth)
          case Single(value) =>
            Deep(
              value.toDigit(depth + 1),
              Empty(),
              suffix,
              m(value.measure(), suffix.measure())
            )
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
            Deep(
              newPrefix,
              newSpine,
              suffix,
              m(newPrefix.measure(), newSpine.measure(), suffix.measure())
            )
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
        Deep(
          prefix,
          spine,
          digit,
          m(prefix.measure(), spine.measure(), digit.measure())
        )
      case None() =>
        spine match {
          case Empty() => prefix.toTree(depth)
          case Single(value) =>
            Deep(
              prefix,
              Empty(),
              value.toDigit(depth + 1),
              m(prefix.measure(), value.measure())
            )
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
            Deep(
              prefix,
              newSpine,
              newSuffix,
              m(prefix.measure(), newSpine.measure(), newSuffix.measure())
            )
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
