import Mathlib

/-!
# A332102: Least m > 0 such that 2*m^n <= Sum_{k < m} k^n.

Source: https://oeis.org/A332102
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A332102 (M. F. Hasler, Apr 18 2020): a(n) =
round(n/log(3/2) + 3).

Conventions:
* The sequence has offset 0 (data 3, 5, 8, 10, 13, 15, 18, 20, 23, 25, 28, 30, ...).
* a(n) is the least m > 0 with 2*m^n <= Sum_{k < m} k^n, where the sum is over the positive
  integers k = 1, ..., m-1 (`Finset.Ico 1 m`); this is the reading of the OEIS example for n = 0
  (Sum_{k<m} k^0 = m - 1). It is stated with `IsLeast`.
* log is the natural logarithm `Real.log` and round is `round : ℝ → ℤ`; the value n/log(3/2) + 3
  is never a half-integer for n > 0 since log(3/2) is irrational, so the rounding convention plays
  no role. The conjecture is stated for all n >= 0 (the offset of the sequence).
-/

namespace OMA.S_oeis_a332102

/-- The conjecture recorded in A332102. -/
theorem main : ∀ n : ℕ, ∃ m : ℕ,
    IsLeast {m : ℕ | 0 < m ∧ 2 * m ^ n ≤ ∑ k ∈ Finset.Ico 1 m, k ^ n} m ∧
    (m : ℤ) = round ((n : ℝ) / Real.log (3 / 2) + 3) := by
  sorry

end OMA.S_oeis_a332102
