import FormalConjectures.OEIS.«181082»

open PowerSeries OeisA181082 Finset

theorem OMA.solution : type_of% @OeisA181082.a_3 := by
  rw [a, hannaExp, coeff_subst' ⟨1, rfl⟩,
    finsum_eq_sum_of_support_subset _ (s := {0,1,2,3}) fun d ↦ Not.imp_symm fun h ↦ by
      simp [X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 rfl : X ∣ hannaLog _) d) 3 (by grind)]]
  norm_num [pow_succ, coeff_mul, Nat.antidiagonal_succ, hannaLog, sum_Icc_succ_top]
