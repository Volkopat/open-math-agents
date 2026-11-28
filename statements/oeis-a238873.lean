import Mathlib

/-!
# A238873: Number of superdiagonal partitions: partitions (p1, p2, p3, ...) of n such that pi >= i.

Source: https://oeis.org/A238873
Credit: @esracummings31-blip

The initial interval of x is {1, ..., x}. A sequence of nonempty sets is choosable iff one can choose
a different element from each set. A partition y = (y_1 ≥ ... ≥ y_k) has choosable initial intervals
iff there are pairwise distinct z_1, ..., z_k with 1 ≤ z_i ≤ y_i (the order of the parts is
irrelevant; we use the weakly decreasing listing). A sequence (y_1, ..., y_k) is superdiagonal iff
y_i ≥ i for all i; the reversed partition lists the parts in weakly increasing order.

Here the parts p1 ≤ p2 ≤ ... are listed in weakly increasing order (the data 1, 1, 1, 2, 3, 3, 5, ...
require this; for the conventional weakly decreasing order one gets A003114, as noted in the entry).

Conjecture (Gus Wiseman, Sep 26 2025): a(n) is also the number of integer partitions y of n with
choosable initial intervals.
-/

namespace OMA.S_oeis_a238873

/-- The parts of a partition in weakly decreasing order. -/
def parts (n : ℕ) (p : Nat.Partition n) : List ℕ := p.parts.sort (· ≥ ·)

/-- Choosable initial intervals: an injective choice `z i ∈ {1, ..., y i}`. -/
def Choosable (y : List ℕ) : Prop :=
  ∃ z : Fin y.length → ℕ, Function.Injective z ∧ ∀ i, 1 ≤ z i ∧ z i ≤ y.get i

/-- Superdiagonal: `y_i ≥ i` (1-indexed). -/
def Superdiagonal (y : List ℕ) : Prop :=
  ∀ i : Fin y.length, i.val + 1 ≤ y.get i

/-- A238873: partitions of `n` whose weakly increasing listing is superdiagonal. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {p : Nat.Partition n // Superdiagonal (parts n p).reverse}

theorem main : ∀ n : ℕ,
    a n = Nat.card {p : Nat.Partition n // Choosable (parts n p)} := by
  sorry

end OMA.S_oeis_a238873
