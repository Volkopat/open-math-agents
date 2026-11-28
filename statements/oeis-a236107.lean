import Mathlib

/-!
# OEIS A236107: Nonprimes whose divisors are partition numbers.

Source: https://oeis.org/A236107
Credit: @unserus

OEIS (J. E. Schoenfield): "Conjecture: no terms exist beyond 77."
The known terms are `1, 15, 22, 77`. A partition number is `p(k)`, the number of partitions of
some `k` (`1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, ...`), here `Fintype.card (Nat.Partition k)`.
The terms are positive integers that are not prime (so `1` counts, as in the data).
-/

namespace OMA.S_oeis_a236107

/-- `m` is a partition number: `m = p(k)` for some `k`. -/
def IsPartitionNumber (m : ℕ) : Prop := ∃ k : ℕ, m = Fintype.card (Nat.Partition k)

/-- The terms of A236107: positive nonprimes all of whose divisors are partition numbers. -/
def a236107Set : Set ℕ :=
  {n : ℕ | 0 < n ∧ ¬ n.Prime ∧ ∀ d ∈ n.divisors, IsPartitionNumber d}

/-- No term of A236107 exceeds `77`. -/
theorem main : ∀ n ∈ a236107Set, n ≤ 77 := by
  sorry

end OMA.S_oeis_a236107
