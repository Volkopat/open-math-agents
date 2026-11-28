import FormalConjectures.OEIS.«183129»

open PowerSeries OeisA183129 Finset

theorem OMA.solution : type_of% @OeisA183129.a_3 := by
  have h0 (f) : constantCoeff (hannaLog f) = 0 := by simp [hannaLog]
  rw [a, hannaExp, coeff_subst' (.of_constantCoeff_zero' (h0 _)),
    finsum_eq_sum_of_support_subset _ (s := range 4) fun d hd => by_contra fun h => hd <| by
      simp [X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 (h0 _)) d) 3 (by simp at h; omega)]]
  norm_num [sum_range_succ, pow_succ, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, hannaLog,
    sum_Icc_succ_top]
