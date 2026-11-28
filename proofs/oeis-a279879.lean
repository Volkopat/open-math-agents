import OMAStatements.S_oeis_a279879

open OMA.S_oeis_a279879 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 8 = 7 * a (8 - 2) - 14 * a (8 - 4) + 8 * a (8 - 6))
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2)) =
      (1 + 2 * X - 5 * X ^ 2 - 2 * X ^ 3 + 7 * X ^ 4 - 14 * X ^ 6 + 8 * X ^ 8 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-7 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (14 : ℤ) • (PowerSeries.mk a * (X ^ 4 : PowerSeries ℤ)) +
        (-8 : ℤ) • (PowerSeries.mk a * (X ^ 6 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (2 : ℤ) • (X ^ 1 : PowerSeries ℤ) +
        (-5 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (-2 : ℤ) • (X ^ 3 : PowerSeries ℤ) +
        (7 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (-14 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (8 : ℤ) • (X ^ 8 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 8) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279879.main) := by
  intro h
  exact coefficient_contradiction a (h.1 8 (by decide)) h.2
