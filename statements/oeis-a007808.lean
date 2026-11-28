import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace OMA.S_oeis_a007808

/-- OEIS A007808: `a(0) = 1`, `a(1) = 1`, and `a(k + 1) = (k + 1) * a(k) + ∑_{j=1}^k a(j)`
for `k ≥ 1`. -/
def a007808 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => (k + 2) * a007808 (k + 1) + ∑ j : Fin (k + 1), a007808 (j.val + 1)
termination_by n => n
decreasing_by
  · omega
  · have := j.isLt; omega

/-- Simon Plouffe's conjectures for OEIS A007808 (corrected by Alper Ferudun):
1. For every `n ≥ 1`, `a(n) = round(n! * n * (e - 2))`.
2. Exponential generating function: for all `x ∈ ℝ` with `|x| < 1`,
   `HasSum (fun n => (a007808 n : ℝ) / n! * x ^ n) (1 + (-(x ^ 2 + 1) * Real.exp (-x) + 1) * Real.exp x / (-1 + x) ^ 2)`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → round ((n.factorial : ℝ) * (n : ℝ) * (Real.exp 1 - 2)) = (a007808 n : ℤ)) ∧
    (∀ x : ℝ, |x| < 1 →
      HasSum (fun n : ℕ => (a007808 n : ℝ) / (n.factorial : ℝ) * x ^ n)
        (1 + (-(x ^ 2 + 1) * Real.exp (-x) + 1) * Real.exp x / (-1 + x) ^ 2)) := by
  sorry

end OMA.S_oeis_a007808
