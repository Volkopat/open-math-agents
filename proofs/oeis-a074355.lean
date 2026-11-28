import OMAStatements.S_oeis_a074355

namespace OMA.P_oeis_a074355

open OMA.S_oeis_a074355 Polynomial

lemma nu0 : nu 1 3 0 = 1 := rfl
lemma nu1 : nu 1 3 1 = 1 := by simp [nu]
lemma nu2 : nu 1 3 2 = C 4 := by
  rw [nu, nu1, nu0]; simp; norm_num
lemma nu3 : nu 1 3 3 = C 7 + C 3 * X := by
  rw [nu, nu2, nu1]; simp [Finset.sum_range_succ]; ring_nf
lemma nu4 : nu 1 3 4 = C 19 + C 15 * X + C 12 * X ^ 2 := by
  rw [nu, nu3, nu2]; simp [Finset.sum_range_succ]; ring_nf

lemma a0 : a 0 = 0 := by simp [a, nu0, coeff_one]
lemma a1 : a 1 = 0 := by simp [a, nu1, coeff_one]
lemma a2 : a 2 = 0 := by simp [a, nu2]
lemma a3 : a 3 = 3 := by simp [a, nu3, coeff_X]
lemma a4 : a 4 = 15 := by simp [a, nu4, coeff_X]

end OMA.P_oeis_a074355

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a074355.main) := by
  intro h
  have hd : (1 - 3 * (PowerSeries.X : PowerSeries ℤ) - 3 * PowerSeries.X ^ 2) ^ 2 =
      PowerSeries.C 1 - PowerSeries.C 6 * PowerSeries.X + PowerSeries.C 3 * PowerSeries.X ^ 2 +
        PowerSeries.C 18 * PowerSeries.X ^ 3 + PowerSeries.C 9 * PowerSeries.X ^ 4 := by
    simp only [map_one, map_ofNat]; ring
  have hr : (9 * PowerSeries.X ^ 4 + 3 * PowerSeries.X ^ 3 : PowerSeries ℤ) =
      PowerSeries.C 9 * PowerSeries.X ^ 4 + PowerSeries.C 3 * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]
  rw [hd, hr] at h
  have e := congrArg (PowerSeries.coeff 4) h
  rw [PowerSeries.coeff_mul] at e
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_C, PowerSeries.coeff_X, PowerSeries.coeff_mk] at e
  simp [Finset.Nat.antidiagonal_succ, OMA.P_oeis_a074355.a0, OMA.P_oeis_a074355.a1,
    OMA.P_oeis_a074355.a2, OMA.P_oeis_a074355.a3, OMA.P_oeis_a074355.a4] at e
