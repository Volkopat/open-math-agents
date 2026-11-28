import Mathlib

/-!
# A247034: Smallest integer x such that the number of integers y<x satisfying sigma(y)/y > sigma(x)/x is exactly n.

Source: https://oeis.org/A247034
Credit: @eltociear

`a(n)` (offset 0) is the least positive integer `x` such that exactly `n` positive integers
`y < x` satisfy `σ(y)/y > σ(x)/x` (`a(0) = 1`, `a(1) = 3`, `a(2) = 10`). The entry conjectures:

  a(n) exists for all n.

`main` states that for every `n` some `x ≥ 1` has exactly `n` such `y`. The ratios are compared
in `ℚ`; `σ` is `ArithmeticFunction.sigma 1`.
-/

namespace OMA.S_oeis_a247034

/-- The abundancy index `σ(m)/m` as a rational number. -/
def abundancy (m : ℕ) : ℚ := (ArithmeticFunction.sigma 1 m : ℚ) / m

/-- The number of `y ∈ [1, x)` with `σ(y)/y > σ(x)/x`. -/
def count (x : ℕ) : ℕ := ((Finset.Ico 1 x).filter (fun y => abundancy x < abundancy y)).card

/-- The conjecture in OEIS A247034: for every `n` there is `x ≥ 1` with exactly `n` positive
`y < x` satisfying `σ(y)/y > σ(x)/x`. -/
theorem main : ∀ n : ℕ, ∃ x : ℕ, 1 ≤ x ∧ count x = n := by
  sorry

end OMA.S_oeis_a247034
