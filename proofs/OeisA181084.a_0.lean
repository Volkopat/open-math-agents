import FormalConjectures.OEIS.«181084»

open PowerSeries OeisA181084

theorem OMA.solution : type_of% @OeisA181084.a_0 := by
  rw [a, hannaExp, coeff_subst' (.of_constantCoeff_zero' (by simp [hannaLog])),
    finsum_eq_single _ 0] <;> simp_all [hannaLog]
