import Mathlib

/-!
# A361197: a(n) is the number of equations in the set {x^2 + 2y^2 = n, 2x^2 + 3y^2 = n, ..., k*x^2 + (k+1)*y^2 = n, ..., n*x^2 + (n+1)*y^2 = n} which admit at least one nonnegative integer solution.

Source: https://oeis.org/A361197
Credit: @eltociear

`a(n)` (offset 1) counts the `k ∈ [1, n]` such that `k x^2 + (k + 1) y^2 = n` has a solution in
nonnegative integers `x, y`. The entry conjectures:

  a(n) = 2 for infinitely many n.

`main` states that the set of `n ≥ 1` with `a(n) = 2` is infinite.
-/

namespace OMA.S_oeis_a361197

/-- `k x^2 + (k + 1) y^2 = n` has a nonnegative integer solution. -/
def Solvable (n k : ℕ) : Prop := ∃ x y : ℕ, k * x ^ 2 + (k + 1) * y ^ 2 = n

open Classical in
/-- OEIS A361197. -/
noncomputable def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun k => Solvable n k)).card

/-- The conjecture in OEIS A361197: `a(n) = 2` for infinitely many `n`. -/
theorem main : {n : ℕ | 1 ≤ n ∧ a n = 2}.Infinite := by
  sorry

end OMA.S_oeis_a361197
