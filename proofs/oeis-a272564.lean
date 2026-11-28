import OMAStatements.S_oeis_a272564

open OMA.S_oeis_a272564 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 7 = 3 * a (7 - 2) - 3 * a (7 - 4) + a (7 - 6))
    (hg : PowerSeries.mk a * ((1 - X) ^ 3 * (1 + X) ^ 3) =
      (1 + 8 * X + 2 * X ^ 2 + 20 * X ^ 3 + X ^ 4 + 4 * X ^ 5 - 4 * X ^ 7 - 4 * X ^ 8 + 8 * X ^ 9
       - 4 * X ^ 11 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-3 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (3 : ℤ) • (PowerSeries.mk a * (X ^ 4 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 6 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (8 : ℤ) • (X ^ 1 : PowerSeries ℤ) +
        (2 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (20 : ℤ) • (X ^ 3 : PowerSeries ℤ) +
        (1 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 5 : PowerSeries ℤ) +
        (-4 : ℤ) • (X ^ 7 : PowerSeries ℤ) +
        (-4 : ℤ) • (X ^ 8 : PowerSeries ℤ) +
        (8 : ℤ) • (X ^ 9 : PowerSeries ℤ) +
        (-4 : ℤ) • (X ^ 11 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 7) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a272564.main) := by
  intro h
  exact coefficient_contradiction a (h.2.2.2.1 7 (by decide)) h.2.2.2.2
