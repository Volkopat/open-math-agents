import FormalConjectures.OEIS.«158110»

open PowerSeries OeisA158110

theorem OMA.solution : type_of% @OeisA158110.a_2 := by
  have h0 : constantCoeff (logSeries 2 3) = 0 := by simp [logSeries]
  rw [a, coeff_subst' (.of_constantCoeff_zero' h0), finsum_eq_sum_of_support_subset _
    (s := Finset.range 3) fun d hd => by_contra fun h => hd <| by
      simp [X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 h0) d) 2 (by simp at h; omega)]]
  simp [Finset.sum_range_succ, pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, logSeries]
  norm_num
