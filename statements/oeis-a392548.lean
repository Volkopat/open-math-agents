import Mathlib

/-!
# A392548: least k such that y^2 = x^3 - k^2 has exactly n integer solutions with y ≥ 0

Source: https://oeis.org/A392548
Credit: @gblacher2

A392548 (Zhining Yang), offset 0: a(n) is the least positive integer k such that Mordell's
equation y^2 = x^3 - k^2 has exactly n integer solutions with y >= 0.
Data: 3, 1, 2, 10, 80, 530, 26, 1160, 208, 1664, 730, ...
Conjecture (in the entry): a(n) is even for all n > 1.

Conventions:
* A solution is a pair `(x, y)` of integers with `y ≥ 0` and `y^2 = x^3 - k^2`.
  For each `k > 0` there are finitely many (Siegel), so `Set.ncard` counts them.
* The entry says "a(22) > 10^8 if it exists", so a term may not exist. The conjecture is stated
  for the terms that exist: for every `n > 1`, if `k` is the least positive integer whose equation
  has exactly `n` such solutions, then `k` is even.
* Checked numerically (searching `x ≤ 10^5`, `k ≤ 100`): the least `k` with exactly
  0, 1, 2, 3, 4, 6 solutions is 3, 1, 2, 10, 80, 26, and for `k = 26` the solutions are
  (10, 18), (13, 39), (26, 130), (130, 1482), (338, 6214), (901, 27045), as in the entry.
-/

namespace OMA.S_oeis_a392548

/-- The integer solutions `(x, y)` of `y^2 = x^3 - k^2` with `y ≥ 0`. -/
def solutions (k : ℕ) : Set (ℤ × ℤ) :=
  {p | 0 ≤ p.2 ∧ p.2 ^ 2 = p.1 ^ 3 - (k : ℤ) ^ 2}

/-- For every `n > 1`, the least positive integer `k` such that `y^2 = x^3 - k^2` has exactly
`n` integer solutions with `y ≥ 0` (when such a `k` exists) is even. -/
theorem main : ∀ n : ℕ, 1 < n → ∀ k : ℕ,
    IsLeast {m : ℕ | 0 < m ∧ (solutions m).ncard = n} k → Even k := by
  sorry

end OMA.S_oeis_a392548
