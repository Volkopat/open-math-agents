import Mathlib

/-!
# A vanishing hypergeometric series

Zhi-Wei Sun asks whether the partial sums of the following series converge to zero.
Source: https://mathoverflow.net/questions/506695
Formalization: @petrovortex
-/

namespace OMA.S_mo_506695

open scoped BigOperators

noncomputable def summand (k : ℕ) : ℝ :=
  let x : ℝ := k
  (Nat.choose (2 * k) k : ℝ) * (16 : ℝ) ^ k *
      (1656 * x ^ 4 - 2604 * x ^ 3 + 1158 * x ^ 2 - 229 * x + 15) /
    (x ^ 2 * (2 * x - 1) ^ 2 * (6 * x - 1) * (6 * x - 5) *
      (Nat.choose (6 * k) (3 * k) : ℝ) * (Nat.choose (3 * k) k : ℝ))

/-- The sum from `k = 1` through `N` tends to zero as `N` tends to infinity. -/
theorem main :
    Filter.Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N, summand (j + 1))
      Filter.atTop (nhds (0 : ℝ)) := by
  sorry

end OMA.S_mo_506695
