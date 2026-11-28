import OMAStatements.S_oeis_a285612

open OMA.S_oeis_a285612 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 4 = a (4 - 1) + 10 * a (4 - 2) - 10 * a (4 - 3))
    (hg : PowerSeries.mk a * ((1 - X) * (1 - 10 * X ^ 2)) =
      (1 - X ^ 2 + 10 * X ^ 4 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 1 : PowerSeries ℤ)) +
        (-10 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (10 : ℤ) • (PowerSeries.mk a * (X ^ 3 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (-1 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (10 : ℤ) • (X ^ 4 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 4) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285612.main) := by
  intro h
  exact coefficient_contradiction a (h.2.2.2 4 (by decide)) h.1
