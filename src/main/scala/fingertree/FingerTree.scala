package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

/// This file defines the data structure for the finger tree, the actual object
/// of interest in our project. Here, we define operations consisting of appending
/// to, removing from, and viewing from both ends of the tree, as well concatenating
/// two tree together. The case classes of FingerTree[T] are found at the end of
/// the file.

sealed trait FingerTree[T, M]:
  import NodeHelpers._
  import DigitHelpers._
  import TreeHelpers._

  /// ***INVARIANT FUNCTIONS*** ///

  /// Checks the invariant that the tree is composed of fully balanced
  /// subtrees of increasing depth at each progressive level
  def isWellFormed(depth: BigInt)(implicit m: Measure[T, M]): Boolean = {
    require(depth >= 0 && m.isValid)

    this match {
      case Empty()       => true
      case Single(value) => value.isWellFormed(depth)
      case Deep(prefix, spine, suffix, measure) =>
        prefix.isWellFormed(depth) &&
        spine.isWellFormed(depth + 1) &&
        suffix.isWellFormed(depth) &&
        measure == m(m(prefix.measure(), spine.measure()), suffix.measure())
    }
  }

  /// A wrapper around isWellFormed(BigInt), starting the check from the
  /// top-most level of the tree
  def isWellFormed(implicit m: Measure[T, M]): Boolean = {
    require(m.isValid)
    this.isWellFormed(0)
  }

  /// ***CONVERSION FUNCTIONS*** ///

  def toTreeL[T, M](
      depth: BigInt,
      elems: List[Node[T, M]]
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        elems.forall(_.isWellFormed(depth))
    )

    elems match {
      case Nil()      => Empty()
      case Cons(h, t) => toTreeL(depth, t).addL(h, depth)
    }
  }.ensuring(res => res.isWellFormed(depth))

  /// Constructs a tree from a list, adding repeatedly to the left of the tree
  def toTreeL[T, M](
      elems: List[T]
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(m.isValid)

    elems match {
      case Nil()      => Empty()
      case Cons(h, t) => toTreeL(t).addL(h)
    }
  }.ensuring(res =>
    res.isWellFormed(0) &&
      res.toListL() == elems
  )

  /// Constructs a tree from a list, adding repeatedly to the right of the tree
  def toTreeR[T, M](
      elems: List[T]
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(m.isValid)

    elems match {
      case Nil()      => Empty()
      case Cons(h, t) => toTreeR(t).addR(h)
    }
  }.ensuring(res =>
    res.isWellFormed(0) &&
      res.toListR() == elems
  )

  /// Constructs a list from a tree, according to an in-order traversal
  def toListL(depth: BigInt)(implicit m: Measure[T, M]): List[T] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Empty()   => Nil()
      case Single(a) => a.toListL(depth)
      case Deep(prefix, spine, suffix, _) => {
        ListLemmas.reverseConcat(
          prefix.toListL(depth),
          spine.toListL(depth + 1)
        )
        ListLemmas.reverseConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )

        prefix.toListL(depth) ++ spine.toListL(depth + 1)
          ++ suffix.toListL(depth)
      }
    }
  }.ensuring(res => res.reverse == this.toListR(depth))

  /// A wrapper around toListL(BigInt), starting from the top-most level of the tree
  def toListL()(implicit m: Measure[T, M]): List[T] = {
    require(m.isValid && this.isWellFormed(0))

    this.toListL(0)
  }.ensuring(res => res.reverse == this.toListR())

  /// Constructs a list from a tree, according to a reversed in-order traversal
  def toListR(depth: BigInt)(implicit m: Measure[T, M]): List[T] = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Empty()   => Nil()
      case Single(a) => a.toListR(depth)
      case Deep(prefix, spine, suffix, _) =>
        suffix.toListR(depth) ++ spine.toListR(depth + 1)
          ++ prefix.toListR(depth)
    }
  }

  /// A wrapper around toListR(BigInt), starting from the top-most level of the tree
  def toListR()(implicit m: Measure[T, M]): List[T] = {
    require(m.isValid && this.isWellFormed(0))

    this.toListR(0)
  }

  /// ***3.2 DEQUE OPERATIONS*** ///

  /// Adds a value to the left end of the tree
  private def addL(value: Node[T, M], depth: BigInt)(implicit
      m: Measure[T, M]
  ): FingerTree[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        this.isWellFormed(depth) &&
        value.isWellFormed(depth)
    )

    this match {
      case Empty() =>
        check(m(value.measure(), m.zero) == value.measure())
        Single(value)
      case Single(existingValue) =>
        check(m(value.measure(), m.zero) == value.measure())
        Deep(
          makeDigit(value, depth),
          Empty(),
          makeDigit(existingValue, depth),
          m(value.measure(), existingValue.measure())
        )
      case Deep(Digit1(a), spine, suffix, _) => {
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          a.toListR(depth),
          value.toListR(depth)
        )

        val newPrefix = makeDigit(value, a, depth)
        check(
          m(
            value.measure(),
            m(m(a.measure(), spine.measure()), suffix.measure())
          ) == m(
            m(m(value.measure(), a.measure()), spine.measure()),
            suffix.measure()
          )
        )
        makeDeep(newPrefix, spine, suffix, depth)
      }
      case Deep(Digit2(a, b, _), spine, suffix, _) => {
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          b.toListL(depth),
          spine.toListL(depth + 1)
        )
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth) ++ spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          b.toListR(depth),
          a.toListR(depth),
          value.toListR(depth)
        )

        val newPrefix = makeDigit(value, a, b, depth)
        makeDeep(newPrefix, spine, suffix, depth)
      }
      case Deep(Digit3(a, b, c, _), spine, suffix, _) => {
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          c.toListR(depth) ++ b.toListR(depth) ++ a.toListR(depth),
          value.toListR(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          value.toListR(depth)
        )

        val newPrefix = makeDigit(value, a, b, c, depth)
        Deep(
          newPrefix,
          spine,
          suffix,
          m(m(newPrefix.measure(), spine.measure()), suffix.measure())
        )
      }
      case Deep(Digit4(a, b, c, d, _), spine, suffix, _) => {
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth)
            ++ c.toListL(depth) ++ d.toListL(depth),
          spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth),
          spine.toListL(depth + 1)
        )
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.associativeConcat(
          value.toListL(depth) ++ a.toListL(depth),
          b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth),
          spine.toListL(depth + 1)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth),
          spine.toListR(depth + 1),
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          value.toListR(depth)
        )

        val newPrefix = makeDigit(value, a, depth)
        val newSpine = spine.addL(makeNode(b, c, d, depth), depth + 1)
        makeDeep(newPrefix, newSpine, suffix, depth)
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res.toListL(depth) == value.toListL(depth) ++ this.toListL(depth) &&
      res.toListR(depth) == this.toListR(depth) ++ value.toListR(depth) &&
      res.measure() == m(value.measure(), this.measure())
  )

  // Prepends a list of values to the left end of the tree
  private def addL(elems: List[Node[T, M]], depth: BigInt)(implicit
      m: Measure[T, M]
  ): FingerTree[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        this.isWellFormed(depth) &&
        elems.forall(_.isWellFormed(depth))
    )

    elems match {
      case Nil() => this
      case Cons(h, t) => {
        ListLemmas.associativeConcat(
          h.toListL(depth),
          Helpers.toListL(t, depth),
          this.toListL(depth)
        )
        ListLemmas.associativeConcat(
          this.toListR(depth),
          Helpers.toListR(t, depth),
          h.toListR(depth)
        )

        this.addL(t, depth).addL(h, depth)
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res.toListL(depth) ==
      Helpers.toListL(elems, depth) ++ this.toListL(depth) &&
      res.toListR(depth) ==
      this.toListR(depth) ++ Helpers.toListR(elems, depth)
  )

  /// A wrapper around addL(Node[T], BigInt) that begins from the root of the tree
  def addL(value: T)(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(m.isValid && this.isWellFormed(0))

    this.addL(Leaf(value), 0)
  }.ensuring(res =>
    res.isWellFormed(0) &&
      res.toListL(0) == value :: this.toListL(0) &&
      res.toListR(0) == this.toListR(0) :+ value &&
      res.measure() == m(m(value), this.measure())
  )

  /// Adds a value to the right end of the tree
  private def addR(value: Node[T, M], depth: BigInt)(implicit
      m: Measure[T, M]
  ): FingerTree[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        this.isWellFormed(depth) &&
        value.isWellFormed(depth)
    )

    this match {
      case Empty() =>
        MeasureLemmas.leftZero(value.measure())
        Single(value)
      case Single(existingValue) =>
        MeasureLemmas.rightZero(existingValue.measure())
        makeDeep(
          makeDigit(existingValue, depth),
          Empty(),
          makeDigit(value, depth),
          depth
        )
      case Deep(prefix, spine, Digit1(a), _) => {
        ListLemmas.associativeConcat(
          value.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth),
          value.toListL(depth)
        )
        MeasureLemmas.associativity(
          prefix.measure(),
          spine.measure(),
          a.measure(),
          value.measure()
        )

        makeDeep(prefix, spine, makeDigit(a, value, depth), depth)
      }
      case Deep(prefix, spine, Digit2(a, b, _), _) => {
        ListLemmas.associativeConcat(
          value.toListR(depth),
          b.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1)
        )
        ListLemmas.associativeConcat(
          value.toListR(depth),
          b.toListR(depth) ++ a.toListR(depth) ++ spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth),
          b.toListL(depth),
          value.toListL(depth)
        )

        makeDeep(prefix, spine, makeDigit(a, b, value, depth), depth)
      }
      case Deep(prefix, spine, Digit3(a, b, c, _), _) => {
        ListLemmas.associativeConcat(
          value.toListR(depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        ListLemmas.associativeConcat(
          value.toListR(depth),
          c.toListR(depth) ++ b.toListR(depth) ++ a.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          value.toListL(depth)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth),
          value.toListL(depth)
        )

        makeDeep(prefix, spine, makeDigit(a, b, c, value, depth), depth)
      }
      case Deep(prefix, spine, Digit4(a, b, c, d, _), _) => {
        ListLemmas.associativeConcat(
          value.toListR(depth),
          d.toListR(depth) ++ c.toListR(depth)
            ++ b.toListR(depth) ++ a.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        ListLemmas.associativeConcat(
          value.toListR(depth),
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1)
        )
        ListLemmas.associativeConcat(
          value.toListR(depth),
          d.toListR(depth),
          c.toListR(depth),
          b.toListR(depth)
        )
        ListLemmas.associativeConcat(
          value.toListR(depth) ++ d.toListR(depth),
          c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth),
          spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth),
          value.toListL(depth)
        )

        val newSpine = spine.addR(makeNode(a, b, c, depth), depth + 1)
        val newSuffix = makeDigit(d, value, depth)
        makeDeep(prefix, newSpine, newSuffix, depth)
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res.toListR(depth) == value.toListR(depth) ++ this.toListR(depth) &&
      res.toListL(depth) == this.toListL(depth) ++ value.toListL(depth) &&
      res.measure() == m(this.measure(), value.measure())
  )

  /// Appends a list of values to the right end of the tree
  private def addR(elems: List[Node[T, M]], depth: BigInt)(implicit
      m: Measure[T, M]
  ): FingerTree[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        this.isWellFormed(depth) &&
        elems.forall(_.isWellFormed(depth))
    )

    elems match {
      case Nil() => this
      case Cons(h, t) => {
        ListLemmas.associativeConcat(
          Helpers.toListR(t, depth),
          h.toListR(depth),
          this.toListR(depth)
        )
        ListLemmas.associativeConcat(
          this.toListL(depth),
          h.toListL(depth),
          Helpers.toListL(t, depth)
        )

        this.addR(h, depth).addR(t, depth)
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res.toListR(depth) ==
      Helpers.toListR(elems, depth) ++ this.toListR(depth) &&
      res.toListL(depth) ==
      this.toListL(depth) ++ Helpers.toListL(elems, depth)
  )

  /// A wrapper around addR(Node[T], BigInt) that begins from the root of the tree
  def addR(value: T)(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(m.isValid && this.isWellFormed(0))

    ListLemmas.prependListConcat(value, this.toListR(0))
    this.addR(Leaf(value), 0)
  }.ensuring(res =>
    res.isWellFormed(0) &&
      res.toListR(0) == value :: this.toListR(0) &&
      res.toListL(0) == this.toListL(0) :+ value &&
      res.measure() == m(this.measure(), m(value))
  )

  /// Potentially gets "head" of left-ordered list represented by tree
  def headL(implicit m: Measure[T, M]): Option[T] = {
    require(m.isValid && this.isWellFormed(0))

    this match {
      case Empty() => None[T]()
      case Single(Leaf(e)) =>
        ListLemmas.reverseHead(this.toListL(0))

        Some(e)
      case Single(_) => ??? // Should never get here
      case Deep(prefix, spine, suffix, _) =>
        prefix.headL(0) match {
          case Leaf(value) => {
            ListLemmas.reverseHead(this.toListL(0))
            check(Some[T](value) == this.toListL(0).headOption)

            Some(value)
          }
          case _ => ??? // Should never get here
        }
    }
  }.ensuring(res =>
    res.isDefined != this.isEmpty &&
      res == this.toListL(0).headOption &&
      res == this.toListR(0).lastOption
  )

  /// Potentially gets "tail" of left-ordered list represented by tree
  def tailL(implicit m: Measure[T, M]): Option[FingerTree[T, M]] = {
    require(m.isValid && this.isWellFormed(0))

    this.viewL match {
      case ConsV(_, rest) => {
        check(!this.isEmpty)

        Some(rest)
      }
      case NilV() => None()
    }
  }.ensuring(res =>
    res.isDefined != this.isEmpty &&
      (res match {
        case None() => true
        case Some(rest) =>
          rest.isWellFormed(0) &&
          rest.toListL() == this.toListL().tail
      })
  )

  /// Splits a tree into its leftmost element and the rest of the tree
  def viewL(implicit m: Measure[T, M]): View[T, M] = {
    require(m.isValid && this.isWellFormed(0))

    this match {
      case Empty()             => NilV()
      case Single(Leaf(value)) => ConsV(value, Empty())
      case Single(_)           => ??? // Should never get here
      case Deep(prefix, spine, suffix, _) =>
        prefix.headL(0) match {
          case Leaf(value) => {
            check(this.headL == Some[T](value))

            ListLemmas.tailConcat(prefix.toListL(0), spine.toListL(1))
            ListLemmas.tailConcat(
              prefix.toListL(0) ++ spine.toListL(1),
              suffix.toListL(0)
            )

            ConsV(
              value,
              Helpers.deepL(prefix.tailL(0), spine, suffix, 0)
            )
          }
          case _ => ??? // Should never get here
        }
    }
  }.ensuring(res =>
    res.isEmpty == this.isEmpty &&
      (res match {
        case NilV() => true
        case ConsV(head, rest) =>
          rest.isWellFormed(0) &&
          Some[T](head) == this.toListL().headOption &&
          Some[T](head) == this.toListR().lastOption &&
          rest.toListL() == this.toListL().tail &&
          m(m(head), rest.measure()) == this.measure()
      })
  )

  /// Potentially gets "head" of right-ordered list represented by tree,
  /// i.e. last element of left-ordered list represented by tree
  def headR(implicit m: Measure[T, M]): Option[T] = {
    require(m.isValid && this.isWellFormed(0))

    this match {
      case Empty()         => None()
      case Single(Leaf(e)) => Some(e)
      case Single(_)       => ??? // Should never get here
      case Deep(prefix, spine, suffix, _) =>
        suffix.headR(0) match {
          case Leaf(value) => {
            ListLemmas.reverseHead(this.toListR())
            FingerTreeLemmas.treeToListRReverse(this, 0)

            Some(value)
          }
          case _ => ??? // Should never get here
        }
    }
  }.ensuring(res =>
    res.isDefined != this.isEmpty &&
      res == this.toListR(0).headOption &&
      res == this.toListL(0).lastOption
  )

  /// Potentially gets "tail" of right-ordered list represented by tree,
  /// i.e. all except the last element of left-ordered list represented by tree
  def tailR(implicit m: Measure[T, M]): Option[FingerTree[T, M]] = {
    require(m.isValid && this.isWellFormed(0))

    this.viewR match {
      case ConsV(_, rest) => {
        check(!this.isEmpty)

        Some(rest)
      }
      case NilV() => None()
    }
  }.ensuring(res =>
    res.isDefined != this.isEmpty &&
      (res match {
        case None() => true
        case Some(rest) =>
          rest.isWellFormed(0) &&
          rest.toListR() == this.toListR().tail
      })
  )

  /// Splits a tree into its rightmost element and the rest of the tree
  def viewR(implicit m: Measure[T, M]): View[T, M] = {
    require(m.isValid && this.isWellFormed(0))

    this match {
      case Empty()             => NilV()
      case Single(Leaf(value)) => ConsV(value, Empty())
      case Single(_)           => ??? // Should never get here
      case Deep(prefix, spine, suffix, _) =>
        suffix.headR(0) match {
          case Leaf(value) => {
            ListLemmas.tailConcat(suffix.toListR(0), spine.toListR(1))
            ListLemmas.tailConcat(
              suffix.toListR(0) ++ spine.toListR(1),
              prefix.toListR(0)
            )

            ConsV(
              this.headR.get,
              Helpers.deepR(prefix, spine, suffix.tailR(0), 0)
            )
          }
          case _ => ??? // Should never get here
        }
    }
  }.ensuring(res =>
    res.isEmpty == this.isEmpty &&
      (res match {
        case NilV() => true
        case ConsV(head, rest) =>
          rest.isWellFormed(0) &&
          Some[T](head) == this.toListR().headOption &&
          Some[T](head) == this.toListL().lastOption &&
          rest.toListR() == this.toListR().tail &&
          m(rest.measure(), m(head)) == this.measure()
      })
  )

  /// Determines if the tree is empty
  def isEmpty(depth: BigInt)(implicit m: Measure[T, M]): Boolean = {
    require(depth >= 0 && m.isValid && this.isWellFormed(depth))

    this match {
      case Empty() => true
      case _       => false
    }
  }.ensuring(res =>
    res == this.toListL(depth).isEmpty &&
      res == this.toListR(depth).isEmpty
  )

  /// A wrapper around isEmpty(BigInt) that begins from the root of the tree
  def isEmpty(implicit m: Measure[T, M]): Boolean = {
    require(m.isValid && this.isWellFormed(0))

    this.isEmpty(0)
  }.ensuring(res =>
    res == this.toListL().isEmpty &&
      res == this.toListR().isEmpty
  )

  /// ***3.3 CONCATENATION*** ///

  /// Concatenates two trees together, as if concatenating the two underlying sequences
  private def concat(
      elems: List[Node[T, M]],
      other: FingerTree[T, M],
      depth: BigInt
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        this.isWellFormed(depth) &&
        other.isWellFormed(depth) &&
        elems.forall(_.isWellFormed(depth))
    )
    decreases(this)

    (this, other) match {
      case (Empty(), _) => other.addL(elems, depth)
      case (_, Empty()) => this.addR(elems, depth)
      case (Single(e), _) => {
        ListLemmas.associativeConcat(
          this.toListL(depth),
          Helpers.toListL(elems, depth),
          other.toListL(depth)
        )

        other.addL(elems, depth).addL(e, depth)
      }
      case (_, Single(e)) => {
        ListLemmas.associativeConcat(
          other.toListR(depth),
          Helpers.toListR(elems, depth),
          this.toListR(depth)
        )

        this.addR(elems, depth).addR(e, depth)
      }
      case (
            Deep(prefix1, spine1, suffix1, _),
            Deep(prefix2, spine2, suffix2, _)
          ) => {
        val elemsTree1 = suffix1.toNodeList(depth)
        val elemsTree2 = prefix2.toNodeList(depth)

        FingerTreeLemmas.distributeToListLConcat(elemsTree1, elems, depth)
        FingerTreeLemmas.distributeToListLConcat(
          elemsTree1 ++ elems,
          elemsTree2,
          depth
        )
        ListLemmas.associativeConcat(
          prefix1.toListL(depth),
          spine1.toListL(depth + 1),
          suffix1.toListL(depth) ++ Helpers.toListL(elems, depth)
            ++ prefix2.toListL(depth),
          spine2.toListL(depth + 1)
        )
        ListLemmas.associativeConcat(
          prefix1.toListL(depth) ++ spine1.toListL(depth + 1),
          suffix1.toListL(depth),
          Helpers.toListL(elems, depth),
          prefix2.toListL(depth)
        )
        ListLemmas.associativeConcat(
          prefix1.toListL(depth) ++ spine1.toListL(depth + 1)
            ++ suffix1.toListL(depth),
          Helpers.toListL(elems, depth),
          prefix2.toListL(depth),
          spine2.toListL(depth + 1)
        )
        ListLemmas.associativeConcat(
          prefix1.toListL(depth) ++ spine1.toListL(depth + 1)
            ++ suffix1.toListL(depth),
          Helpers.toListL(elems, depth),
          prefix2.toListL(depth) ++ spine2.toListL(depth + 1),
          suffix2.toListL(depth)
        )

        FingerTreeLemmas.distributeToListRConcat(elemsTree1, elems, depth)
        FingerTreeLemmas.distributeToListRConcat(
          elemsTree1 ++ elems,
          elemsTree2,
          depth
        )
        ListLemmas.associativeConcat(
          Helpers.toListR(elemsTree2, depth),
          Helpers.toListR(elems, depth),
          Helpers.toListR(elemsTree1, depth)
        )

        // Verify lemmas on suffix of spine of new tree
        ListLemmas.associativeConcat(
          suffix2.toListR(depth),
          spine2.toListR(depth + 1),
          prefix2.toListR(depth) ++ Helpers.toListR(elems, depth)
            ++ suffix1.toListR(depth),
          spine1.toListR(depth + 1)
        )
        ListLemmas.associativeConcat(
          suffix2.toListR(depth) ++ spine2.toListR(depth + 1),
          prefix2.toListR(depth),
          Helpers.toListR(elems, depth),
          suffix1.toListR(depth)
        )
        ListLemmas.associativeConcat(
          suffix2.toListR(depth) ++ spine2.toListR(depth + 1)
            ++ prefix2.toListR(depth),
          Helpers.toListR(elems, depth),
          suffix1.toListR(depth),
          spine1.toListR(depth + 1)
        )
        ListLemmas.associativeConcat(
          suffix2.toListR(depth) ++ spine2.toListR(depth + 1)
            ++ prefix2.toListR(depth),
          Helpers.toListR(elems, depth),
          suffix1.toListR(depth) ++ spine1.toListR(depth + 1),
          prefix1.toListR(depth)
        )

        ListLemmas.forallConcat(elemsTree1, elems, _.isWellFormed(depth))
        ListLemmas.forallConcat(
          elemsTree1 ++ elems,
          elemsTree2,
          _.isWellFormed(depth)
        )

        val elemsRec = elemsTree1 ++ elems ++ elemsTree2
        check(elemsTree1.size >= 1 && elemsTree2.size >= 1)
        val newElems = Helpers.toNodes(elemsRec, depth)

        val newSpine = spine1.concat(newElems, spine2, depth + 1)
        makeDeep(prefix1, newSpine, suffix2, depth)
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res.toListL(depth) == this.toListL(depth) ++
      Helpers.toListL(elems, depth) ++ other.toListL(depth) &&
      res.toListR(depth) == other.toListR(depth) ++
      Helpers.toListR(elems, depth) ++ this.toListR(depth)
  )

  /// A wrapper around concat(List[Node[T]], FingerTree[T], BigInt)
  /// that begins from the root of the tree
  def concat(
      tree: FingerTree[T, M]
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(m.isValid && this.isWellFormed(0) && tree.isWellFormed(0))

    this.concat(Nil(), tree, 0)
  }.ensuring(res =>
    res.isWellFormed(0) &&
      res.toListL() == this.toListL() ++ tree.toListL() &&
      res.toListR() == tree.toListR() ++ this.toListR()
  )

  /// *** MEASURE *** ///

  def measure()(implicit m: Measure[T, M]): M = {
    require(m.isValid)

    this match {
      case Empty()                => m.zero
      case Single(value)          => value.measure()
      case Deep(_, _, _, measure) => measure
    }
  }

  private def split(depth: BigInt, acc: M)(implicit
      p: M => Boolean,
      m: Measure[T, M]
  ): (FingerTree[T, M], Node[T, M], FingerTree[T, M]) = {
    decreases(this)
    require(
      depth >= 0 &&
        m.isValid &&
        this.isWellFormed(depth) &&
        !p(acc) && p(m(acc, this.measure()))
    )

    this match {
      case Single(value) => (Empty(), value, Empty())
      case Deep(prefix, spine, suffix, _) if p(m(acc, prefix.measure())) =>
        val (pref, elem, suff) = prefix.split(depth, acc, p)
        val previous = pref match {
          case Some(prev) => prev.toTree(depth)
          case None()     => Empty[T, M]()
        }
        (previous, elem, Helpers.deepL(suff, spine, suffix, depth))
      case Deep(prefix, spine, suffix, _) if p(m(acc, prefix.measure())) =>
        check(p(m(m(acc, prefix.measure()), spine.measure())))
        val (pref, elem, suff) =
          spine.split(depth + 1, m(acc, prefix.measure()))
        val (newpref, newelem, newsuff) = elem
          .toDigit(depth)
          .split(depth, m(m(acc, prefix.measure()), pref.measure()), p)
        (
          Helpers.deepR(prefix, pref, newpref, depth),
          newelem,
          Helpers.deepL(newsuff, suff, suffix, depth)
        )
      case Deep(prefix, spine, suffix, _) =>
        val (pref, elem, suff) =
          suffix.split(depth, m(m(acc, prefix.measure()), spine.measure()), p)
        val following = suff match {
          case Some(foll) => foll.toTree(depth)
          case None()     => Empty[T, M]()
        }
        (Helpers.deepR(prefix, spine, pref, depth), elem, following)
      case Empty() =>
        MeasureLemmas.rightZero(acc)
        ???
    }
  }.ensuring { case (pref, elem, suff) =>
    pref.isWellFormed(depth) &&
    suff.isWellFormed(depth) &&
    elem.isWellFormed(depth) &&
    !p(pref.measure()) && p(m(pref.measure(), elem.measure()))
  }

  def split(
      p: M => Boolean
  )(implicit m: Measure[T, M]): (FingerTree[T, M], T, FingerTree[T, M]) = {
    require(
      m.isValid &&
        this.isWellFormed(0) &&
        !p(m.zero) &&
        p(this.measure())
    )

    check(this.measure() == m(m.zero, this.measure()))
    this.split(0, m.zero)(p, m) match {
      case (pref, Leaf(elem), suff) => (pref, elem, suff)
      case (_, _, _)                => ???
    }
  }.ensuring { case (pref, elem, suff) =>
    pref.isWellFormed(0) && suff.isWellFormed(0) &&
    !p(pref.measure()) && p(m(pref.measure(), m(elem)))
  }

/// A FingerTree[T] is either a:
/// - Empty[T](),
/// - Single[T](Node[T]), or
/// - Deep[T](Digit[T], FingerTree[T], Digit[T])
final case class Empty[T, M]() extends FingerTree[T, M]
final case class Single[T, M](value: Node[T, M]) extends FingerTree[T, M]
final case class Deep[T, M](
    prefix: Digit[T, M],
    spine: FingerTree[T, M],
    suffix: Digit[T, M],
    m: M
) extends FingerTree[T, M]

object TreeHelpers {
  def makeDeep[T, M](
      prefix: Digit[T, M],
      spine: FingerTree[T, M],
      suffix: Digit[T, M],
      depth: BigInt
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(
      depth >= 0 &&
        m.isValid &&
        prefix.isWellFormed(depth) &&
        spine.isWellFormed(depth + 1) &&
        suffix.isWellFormed(depth)
    )
    Deep(
      prefix,
      spine,
      suffix,
      m(m(prefix.measure(), spine.measure()), suffix.measure())
    )
  }.ensuring(res =>
    res.isWellFormed(depth) &&
      res.toListL(depth) == suffix.toListL(depth) ++
      spine.toListL(depth + 1) ++ prefix.toListL(depth) &&
      res.toListR(depth) == prefix.toListR(depth) ++
      spine.toListR(depth + 1) ++ suffix.toListR(depth)
  )
}
