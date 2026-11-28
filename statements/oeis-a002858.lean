import Mathlib

/-!
# A002858: Ulam numbers have density zero

Source: https://oeis.org/A002858
Credit: @Bondyboy2001

The Ulam sequence starts with `a 1 = 1` and `a 2 = 2`. Thereafter `a n` is the least
number greater than `a (n - 1)` having exactly one representation as a sum of two distinct
earlier terms. Ulam conjectured that the sequence has natural density zero.
-/

namespace OMA.S_oeis_a002858

open Filter Topology

/-- The number of representations of `m` as `a i + a j` with `1 ≤ i < j ≤ n`. -/
def uniqueSumCount (a : ℕ → ℕ) (n m : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun q => q.1 < q.2 ∧ a q.1 + a q.2 = m).card

/-- `a` is the Ulam sequence, with the conventional OEIS indexing starting at `1`. -/
def IsUlamSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧ ∀ n : ℕ, 3 ≤ n →
    (a (n - 1) < a n ∧ uniqueSumCount a (n - 1) (a n) = 1) ∧
    ∀ m : ℕ, a (n - 1) < m → uniqueSumCount a (n - 1) m = 1 → a n ≤ m

/-- Ulam's conjecture: the sequence has natural density zero. -/
theorem main :
    ∀ a : ℕ → ℕ, IsUlamSeq a →
      Tendsto (fun N : ℕ => ((Set.ncard (Set.range a ∩ Set.Iio N) : ℕ) : ℝ) / N)
        atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a002858
