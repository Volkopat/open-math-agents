import Mathlib

/-!
# A387118: Number of integer partitions of n without choosable initial intervals.

Source: https://oeis.org/A387118
Credit: @esracummings31-blip

The initial interval of x is {1, ..., x}. A sequence of nonempty sets is choosable iff one can choose
a different element from each set. A partition y = (y_1 ≥ ... ≥ y_k) has choosable initial intervals
iff there are pairwise distinct z_1, ..., z_k with 1 ≤ z_i ≤ y_i (the order of the parts is
irrelevant; we use the weakly decreasing listing). A sequence (y_1, ..., y_k) is superdiagonal iff
y_i ≥ i for all i; the reversed partition lists the parts in weakly increasing order.

Conjecture (Gus Wiseman, Oct 04 2025): a(n) is also the number of non-superdiagonal reversed
integer partitions of n.
-/

namespace OMA.S_oeis_a387118

/-- The parts of a partition in weakly decreasing order. -/
def parts (n : ℕ) (p : Nat.Partition n) : List ℕ := p.parts.sort (· ≥ ·)

/-- Choosable initial intervals: an injective choice `z i ∈ {1, ..., y i}`. -/
def Choosable (y : List ℕ) : Prop :=
  ∃ z : Fin y.length → ℕ, Function.Injective z ∧ ∀ i, 1 ≤ z i ∧ z i ≤ y.get i

/-- Superdiagonal: `y_i ≥ i` (1-indexed). -/
def Superdiagonal (y : List ℕ) : Prop :=
  ∀ i : Fin y.length, i.val + 1 ≤ y.get i

/-- A387118: partitions of `n` without choosable initial intervals. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {p : Nat.Partition n // ¬ Choosable (parts n p)}

theorem main : ∀ n : ℕ,
    a n = Nat.card {p : Nat.Partition n // ¬ Superdiagonal (parts n p).reverse} := by
  sorry

end OMA.S_oeis_a387118
