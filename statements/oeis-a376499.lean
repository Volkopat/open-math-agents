import Mathlib

/-!
# Integrality of the quotient array A376499

Source: https://oeis.org/A376499
Underlying sine-power array: https://oeis.org/A376484
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a376499

noncomputable def angle (n j : ℕ) : ℝ := 2*((j:ℝ)+1)*Real.pi/(2*n+1)

noncomputable def entry (n k : ℕ) : ℝ :=
  4^k * ∑ j ∈ Finset.range n, Real.sin (angle n j)^(2*k)

/- The array displayed in A376499 starts at row 1 and power 1. -/
theorem main : ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → ∃ z : ℤ, entry n k / (2*n+1) = z := by
  sorry

end OMA.S_oeis_a376499
