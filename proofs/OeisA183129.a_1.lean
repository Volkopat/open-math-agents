import FormalConjectures.OEIS.«183129»

open PowerSeries OeisA183129

theorem OMA.solution : type_of% @OeisA183129.a_1 := by
  rw [a, hannaExp, coeff_subst' (.of_constantCoeff_zero' (by simp [hannaLog])), finsum_eq_single _ 1]
  · simp [hannaLog]
  · rintro (_ | d) hd <;> simp_all [coeff_one_pow, hannaLog]
