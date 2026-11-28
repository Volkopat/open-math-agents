import OMAStatements.S_oeis_a284175

open OMA.S_oeis_a284175 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 17 = a (17 - 2) + 100000000 * a (17 - 8) - 100000000 * a (17 - 10))
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2) * (1 + 10000 * X ^ 4)) =
      (1 + 100 * X ^ 4 + 10000 * X ^ 6 + 1000 * X ^ 7 - 99009100 * X ^ 8 + 100000000 * X ^ 10
       + 10000000 * X ^ 11 - 91000000 * X ^ 12 + 100000 * X ^ 13 + 100000 * X ^ 14
       + 1000000000 * X ^ 17 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (-100000000 : ℤ) • (PowerSeries.mk a * (X ^ 8 : PowerSeries ℤ)) +
        (100000000 : ℤ) • (PowerSeries.mk a * (X ^ 10 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (100 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (10000 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (1000 : ℤ) • (X ^ 7 : PowerSeries ℤ) +
        (-99009100 : ℤ) • (X ^ 8 : PowerSeries ℤ) +
        (100000000 : ℤ) • (X ^ 10 : PowerSeries ℤ) +
        (10000000 : ℤ) • (X ^ 11 : PowerSeries ℤ) +
        (-91000000 : ℤ) • (X ^ 12 : PowerSeries ℤ) +
        (100000 : ℤ) • (X ^ 13 : PowerSeries ℤ) +
        (100000 : ℤ) • (X ^ 14 : PowerSeries ℤ) +
        (1000000000 : ℤ) • (X ^ 17 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 17) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284175.main) := by
  intro h
  exact coefficient_contradiction a (h.2 17 (by decide)) h.1
