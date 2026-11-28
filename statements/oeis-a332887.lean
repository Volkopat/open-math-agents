import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.NumberTheory.Divisors

/-!
# A332887: Every proper partition-divisor count occurs infinitely often

Source: https://oeis.org/A332887 (Clark Kimberling)
Credit: @Alienchisel

The partition number p(n) counts integer partitions of n. The sequence
counts distinct proper divisors of p(n) greater than 1 which are themselves
partition numbers. Its first index is n = 2.
-/

namespace OMA.S_oeis_a332887

/-- The number of integer partitions of n. -/
noncomputable def partitionNumber (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

/-- The number of proper divisors greater than 1 that occur as partition numbers. -/
noncomputable def partitionDivisorCount (n : ℕ) : ℕ := by
  classical
  exact ((partitionNumber n).properDivisors.filter fun d =>
    1 < d ∧ ∃ j : ℕ, partitionNumber j = d).card

theorem main : ∀ k : ℕ,
    Set.Infinite {n : ℕ | 2 ≤ n ∧ partitionDivisorCount n = k} := by
  sorry

end OMA.S_oeis_a332887
