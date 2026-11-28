import FormalConjectures.OEIS.«158110»

open OeisA158110 PowerSeries

theorem OMA.solution : type_of% @OeisA158110.a_1 := by
  rw [a, coeff_subst' (.of_constantCoeff_zero' (by simp [logSeries])), finsum_eq_single _ 1]
  · simp [coeff_exp, logSeries]
  · rintro (_ | _ | d) hd <;> simp_all [coeff_one_pow, logSeries]
