import Mathlib

/-!
# A388713: Triangle read by rows where T(n,k) is the number of superdiagonal multisets summing to n (reversed partitions of n) with maximum k.

Source: https://oeis.org/A388713
Credit: @esracummings31-blip

The initial interval of x is {1, ..., x}. A sequence of nonempty sets is choosable iff one can choose
a different element from each set. A partition y = (y_1 ≥ ... ≥ y_k) has choosable initial intervals
iff there are pairwise distinct z_1, ..., z_k with 1 ≤ z_i ≤ y_i (the order of the parts is
irrelevant; we use the weakly decreasing listing). A sequence (y_1, ..., y_k) is superdiagonal iff
y_i ≥ i for all i; the reversed partition lists the parts in weakly increasing order.

The maximum is only defined for nonempty partitions (the data has T(0,0) = 0), so both counts below
range over partitions with at least one part; the maximum is `Multiset.sup` of the parts.

Conjecture (Gus Wiseman): T(n,k) is also the number of integer partitions of n with maximum k and
choosable initial intervals.
-/

namespace OMA.S_oeis_a388713

/-- The parts of a partition in weakly decreasing order. -/
def parts (n : ℕ) (p : Nat.Partition n) : List ℕ := p.parts.sort (· ≥ ·)

/-- Choosable initial intervals: an injective choice `z i ∈ {1, ..., y i}`. -/
def Choosable (y : List ℕ) : Prop :=
  ∃ z : Fin y.length → ℕ, Function.Injective z ∧ ∀ i, 1 ≤ z i ∧ z i ≤ y.get i

/-- Superdiagonal: `y_i ≥ i` (1-indexed). -/
def Superdiagonal (y : List ℕ) : Prop :=
  ∀ i : Fin y.length, i.val + 1 ≤ y.get i

/-- A388713: superdiagonal reversed partitions of `n` with maximum `k`. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Nat.card {p : Nat.Partition n // p.parts ≠ 0 ∧ p.parts.sup = k ∧ Superdiagonal (parts n p).reverse}

theorem main : ∀ n k : ℕ,
    T n k = Nat.card {p : Nat.Partition n // p.parts ≠ 0 ∧ p.parts.sup = k ∧ Choosable (parts n p)} := by
  sorry

end OMA.S_oeis_a388713
