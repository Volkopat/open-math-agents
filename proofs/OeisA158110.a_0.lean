import FormalConjectures.OEIS.«158110»

/-! Only the constant exponential term contributes. -/
open PowerSeries OeisA158110 in
theorem OMA.solution : type_of% @OeisA158110.a_0 := by
  rw [a, coeff_subst' (.of_constantCoeff_zero' rfl), finsum_eq_single _ 0] <;>
    simp +contextual [coeff_zero_eq_constantCoeff_apply, logSeries]
