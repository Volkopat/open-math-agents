import OMAStatements.S_oeis_a279501

open OMA.S_oeis_a279501 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 10 = 4 * a (10 - 2) + a (10 - 4) - 4 * a (10 - 6))
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X ^ 2)) =
      (1 + X ^ 2 + 8 * X ^ 4 - 24 * X ^ 6 - 128 * X ^ 10 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-4 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 4 : PowerSeries ℤ)) +
        (4 : ℤ) • (PowerSeries.mk a * (X ^ 6 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (1 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (8 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (-24 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (-128 : ℤ) • (X ^ 10 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 10) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279501.main) := by
  intro h
  exact coefficient_contradiction a (h.1 10 (by decide)) h.2
