import Mathlib

/-!
# Unfriendly partitions

Source: https://www.openproblemgarden.org/op/unfriendly_partitions
Credit: @lzvxck

The source: a partition of the vertex set of a graph is unfriendly if every vertex has at least
as many neighbors in the other classes as in its own. Problem: does every countably infinite
graph have an unfriendly partition into two sets?

(Every finite graph has one; Milner and Shelah gave an uncountable counterexample, so the
countable case is the open one.) The statement below is the affirmative answer; a proof of its
negation would settle the question negatively.

A partition into two sets is encoded as a map `c : V → Bool` (one class is `c = true`, the
other `c = false`; a class may be empty). Neighbours are counted as cardinals, since degrees
may be infinite.
-/

namespace OMA.S_opg_unfriendly_partitions

/-- `c` is an unfriendly partition of `G` into two sets: every vertex `v` has at least as many
neighbours in the other class as in its own (counted as cardinals). -/
def IsUnfriendly {V : Type*} (G : SimpleGraph V) (c : V → Bool) : Prop :=
  ∀ v : V, Cardinal.mk {w : V // G.Adj v w ∧ c w = c v} ≤
    Cardinal.mk {w : V // G.Adj v w ∧ c w ≠ c v}

/-- **Unfriendly partitions.** Every countably infinite graph has an unfriendly partition into
two sets. -/
theorem main : ∀ (V : Type) [Countable V] [Infinite V] (G : SimpleGraph V),
    ∃ c : V → Bool, IsUnfriendly G c := by
  sorry

end OMA.S_opg_unfriendly_partitions
