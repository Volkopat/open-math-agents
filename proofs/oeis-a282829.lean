import OMAStatements.S_oeis_a282829

open OMA.S_oeis_a282829 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 17 = 4 * a (17 - 2) + a (17 - 8) - 4 * a (17 - 10))
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X ^ 2) * (1 + X ^ 4)) =
      (1 + 12 * X ^ 4 + 56 * X ^ 5 - 28 * X ^ 6 - 224 * X ^ 7 + 43 * X ^ 8 + 248 * X ^ 9
       - 156 * X ^ 10 - 992 * X ^ 11 + 416 * X ^ 12 + 3392 * X ^ 13 - 768 * X ^ 14 + 128 * X ^ 15
       - 4096 * X ^ 17 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-4 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 8 : PowerSeries ℤ)) +
        (4 : ℤ) • (PowerSeries.mk a * (X ^ 10 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (12 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (56 : ℤ) • (X ^ 5 : PowerSeries ℤ) +
        (-28 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (-224 : ℤ) • (X ^ 7 : PowerSeries ℤ) +
        (43 : ℤ) • (X ^ 8 : PowerSeries ℤ) +
        (248 : ℤ) • (X ^ 9 : PowerSeries ℤ) +
        (-156 : ℤ) • (X ^ 10 : PowerSeries ℤ) +
        (-992 : ℤ) • (X ^ 11 : PowerSeries ℤ) +
        (416 : ℤ) • (X ^ 12 : PowerSeries ℤ) +
        (3392 : ℤ) • (X ^ 13 : PowerSeries ℤ) +
        (-768 : ℤ) • (X ^ 14 : PowerSeries ℤ) +
        (128 : ℤ) • (X ^ 15 : PowerSeries ℤ) +
        (-4096 : ℤ) • (X ^ 17 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 17) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282829.main) := by
  intro h
  exact coefficient_contradiction a (h.1 17 (by decide)) h.2
