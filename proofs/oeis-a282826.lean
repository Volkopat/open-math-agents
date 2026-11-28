import OMAStatements.S_oeis_a282826

open OMA.S_oeis_a282826 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 17 = a (17 - 2) + 100000000 * a (17 - 8) - 100000000 * a (17 - 10))
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2) * (1 + 10000 * X ^ 4)) =
      (1 + 110 * X ^ 4 + 111 * X ^ 5 + 9990 * X ^ 6 - 111 * X ^ 7 - 98899000 * X ^ 8
       + 1111100 * X ^ 9 + 99899000 * X ^ 10 - 1111100 * X ^ 11 + 10091000 * X ^ 12
       + 10101100 * X ^ 13 - 1100000 * X ^ 14 + 100000000 * X ^ 15 - 100000 * X ^ 17 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (-100000000 : ℤ) • (PowerSeries.mk a * (X ^ 8 : PowerSeries ℤ)) +
        (100000000 : ℤ) • (PowerSeries.mk a * (X ^ 10 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (110 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (111 : ℤ) • (X ^ 5 : PowerSeries ℤ) +
        (9990 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (-111 : ℤ) • (X ^ 7 : PowerSeries ℤ) +
        (-98899000 : ℤ) • (X ^ 8 : PowerSeries ℤ) +
        (1111100 : ℤ) • (X ^ 9 : PowerSeries ℤ) +
        (99899000 : ℤ) • (X ^ 10 : PowerSeries ℤ) +
        (-1111100 : ℤ) • (X ^ 11 : PowerSeries ℤ) +
        (10091000 : ℤ) • (X ^ 12 : PowerSeries ℤ) +
        (10101100 : ℤ) • (X ^ 13 : PowerSeries ℤ) +
        (-1100000 : ℤ) • (X ^ 14 : PowerSeries ℤ) +
        (100000000 : ℤ) • (X ^ 15 : PowerSeries ℤ) +
        (-100000 : ℤ) • (X ^ 17 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 17) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282826.main) := by
  intro h
  exact coefficient_contradiction a (h.1 17 (by decide)) h.2
