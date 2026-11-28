import FormalConjectures.OEIS.«181078»

open PowerSeries OeisA181078 Finset

theorem OMA.solution : type_of% @OeisA181078.a_4 := by
  rw [a, hannaExp, coeff_subst' ⟨1, rfl⟩,
    finsum_eq_sum_of_support_subset _ (s := {0,1,2,3,4}) fun d ↦ Not.imp_symm fun h ↦ by
      simp [X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 rfl : X ∣ hannaLog _) d) 4 (by simp at h; omega)]]
  simp [pow_succ, coeff_mul, Nat.antidiagonal_succ]
  norm_num [hannaLog, sum_Icc_succ_top]
