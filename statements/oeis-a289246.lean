import Mathlib

/-!
# Kimberling's reciprocal series from two Beatty sequences

With φ the golden ratio and s its reciprocal, the denominator has
coefficient (-1)^k times floor((k+1)φ) + floor((k+1)s), with the sign
applied to the entire sum. Its constant coefficient is one, so its
reciprocal is defined over the integers. A289246 asks whether the
coefficients of that reciprocal are strictly increasing from index zero.
Source: https://oeis.org/A289246
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a289246

noncomputable def golden : ℝ := (1 + Real.sqrt 5) / 2

noncomputable def weight (k : ℕ) : ℤ :=
  ⌊((k : ℝ)+1) * golden⌋ + ⌊((k : ℝ)+1) * golden⁻¹⌋

noncomputable def denominator : PowerSeries ℤ :=
  PowerSeries.mk fun k => (-1 : ℤ)^k * weight k

noncomputable def generating : PowerSeries ℤ := PowerSeries.invOfUnit denominator 1

noncomputable def a (n : ℕ) : ℤ := PowerSeries.coeff n generating

theorem main : StrictMono a := by
  sorry

end OMA.S_oeis_a289246
