import FormalConjectures.OEIS.«181082»

open PowerSeries OeisA181082

theorem OMA.solution : type_of% @OeisA181082.a_0 := by
  rw [a, hannaExp, coeff_subst' (.of_constantCoeff_zero' (by simp [hannaLog])),
    finsum_eq_single _ 0] <;> simp_all [hannaLog]
