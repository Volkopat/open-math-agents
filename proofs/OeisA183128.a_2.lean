import FormalConjectures.OEIS.«183128»

open PowerSeries OeisA183128 Finset

theorem OMA.solution : type_of% @OeisA183128.a_2 := by
  have h0 (f) : constantCoeff (hannaLog f) = 0 := by simp [hannaLog]
  rw [a, hannaExp, coeff_subst' (.of_constantCoeff_zero' (h0 _)),
    finsum_eq_sum_of_support_subset _ (s := range 3) fun d hd => by_contra fun h => hd <| by
      simp [X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 (h0 _)) d) 2 (by simp at h; omega)]]
  norm_num [sum_range_succ, pow_succ, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, hannaLog,
    sum_Icc_succ_top]
