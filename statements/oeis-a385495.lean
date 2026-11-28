import Mathlib

/-!
# OEIS A385495 and the leading digit of the Riemann zeta tail

Source: https://oeis.org/A385495
Comparison sequence: https://oeis.org/A111395
Credit: @Mapika

Ripà asks whether the first significant decimal digit of ζ(n) − 1 agrees with
that of 5ⁿ for every integer n ≥ 10. For n ≥ 2, the defining Dirichlet series
for ζ(n) has first term 1. Removing it leaves the sum indexed by 2, 3, …
-/

namespace OMA.S_oeis_a385495

/-- The ordinary zeta tail, expressed by its defining series for n ≥ 2. -/
noncomputable def zetaTail (n : ℕ) : ℝ := ∑' j : ℕ, (((j + 2 : ℕ) : ℝ)⁻¹) ^ n

/-- The first significant decimal digit of a positive real number. -/
noncomputable def ld (x : ℝ) : ℤ := ⌊x / 10 ^ ⌊Real.logb 10 x⌋⌋

theorem main : ∀ n : ℕ, 10 ≤ n → ld (zetaTail n) = ld ((5 : ℝ) ^ n) := by
  sorry

end OMA.S_oeis_a385495
