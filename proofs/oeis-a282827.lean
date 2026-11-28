import OMAStatements.S_oeis_a282827

open OMA.S_oeis_a282827 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 17 = 100 * a (17 - 2) + a (17 - 8) - 100 * a (17 - 10))
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + X ^ 2) * (1 + X ^ 4)) =
      (1 + 1100 * X ^ 4 + 111000 * X ^ 5 - 99900 * X ^ 6 - 11100000 * X ^ 7 + 101099 * X ^ 8
       + 11111000 * X ^ 9 - 10099900 * X ^ 10 - 1111100000 * X ^ 11 + 910100000 * X ^ 12
       + 110101000000 * X ^ 13 - 1100000000 * X ^ 14 + 10000000 * X ^ 15 - 1000000000000 * X ^ 17 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-100 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 8 : PowerSeries ℤ)) +
        (100 : ℤ) • (PowerSeries.mk a * (X ^ 10 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (1100 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (111000 : ℤ) • (X ^ 5 : PowerSeries ℤ) +
        (-99900 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (-11100000 : ℤ) • (X ^ 7 : PowerSeries ℤ) +
        (101099 : ℤ) • (X ^ 8 : PowerSeries ℤ) +
        (11111000 : ℤ) • (X ^ 9 : PowerSeries ℤ) +
        (-10099900 : ℤ) • (X ^ 10 : PowerSeries ℤ) +
        (-1111100000 : ℤ) • (X ^ 11 : PowerSeries ℤ) +
        (910100000 : ℤ) • (X ^ 12 : PowerSeries ℤ) +
        (110101000000 : ℤ) • (X ^ 13 : PowerSeries ℤ) +
        (-1100000000 : ℤ) • (X ^ 14 : PowerSeries ℤ) +
        (10000000 : ℤ) • (X ^ 15 : PowerSeries ℤ) +
        (-1000000000000 : ℤ) • (X ^ 17 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 17) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282827.main) := by
  intro h
  exact coefficient_contradiction a (h.1 17 (by decide)) h.2
