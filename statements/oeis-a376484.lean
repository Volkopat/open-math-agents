import Mathlib

/-!
# Integrality of the sine-power array A376484

Source: https://oeis.org/A376484
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a376484

noncomputable def angle (n j : ℕ) : ℝ := 2*((j:ℝ)+1)*Real.pi/(2*n+1)

noncomputable def entry (n k : ℕ) : ℝ :=
  4^k * ∑ j ∈ Finset.range n, Real.sin (angle n j)^(2*k)

theorem main : ∀ n k : ℕ, ∃ z : ℤ, entry n k = z := by
  sorry

end OMA.S_oeis_a376484
