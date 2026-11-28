import Mathlib

/-!
# Increasing coefficients in Kimberling's reciprocal series

For each index k the denominator coefficient is (-1)^k times the floor of
(k+1) times the specified slope. Its constant coefficient is one.
Clark Kimberling asks whether the coefficients of its reciprocal increase
strictly, starting at index zero. Source: https://oeis.org/A288234
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a288234

noncomputable def weight (r : ℝ) (n : ℕ) : ℚ := (⌊((n : ℝ) + 1) * r⌋ : ℤ)

noncomputable def denominator (r : ℝ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (-1 : ℚ)^n * weight r n

noncomputable def a (r : ℝ) (n : ℕ) : ℚ :=
  PowerSeries.coeff n (denominator r)⁻¹

theorem main : StrictMono (a (-1 + Real.sqrt 7)) := by
  sorry

end OMA.S_oeis_a288234
