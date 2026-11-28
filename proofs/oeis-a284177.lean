import OMAStatements.S_oeis_a284177

open OMA.S_oeis_a284177 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 17 = a (17 - 2) + 256 * a (17 - 8) - 256 * a (17 - 10))
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * (1 + 16 * X ^ 4)) =
      (1 + 4 * X ^ 4 + 16 * X ^ 6 + 8 * X ^ 7 - 204 * X ^ 8 + 256 * X ^ 10 + 128 * X ^ 11
       - 192 * X ^ 12 + 32 * X ^ 13 + 32 * X ^ 14 + 512 * X ^ 17 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (-256 : ℤ) • (PowerSeries.mk a * (X ^ 8 : PowerSeries ℤ)) +
        (256 : ℤ) • (PowerSeries.mk a * (X ^ 10 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (16 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (8 : ℤ) • (X ^ 7 : PowerSeries ℤ) +
        (-204 : ℤ) • (X ^ 8 : PowerSeries ℤ) +
        (256 : ℤ) • (X ^ 10 : PowerSeries ℤ) +
        (128 : ℤ) • (X ^ 11 : PowerSeries ℤ) +
        (-192 : ℤ) • (X ^ 12 : PowerSeries ℤ) +
        (32 : ℤ) • (X ^ 13 : PowerSeries ℤ) +
        (32 : ℤ) • (X ^ 14 : PowerSeries ℤ) +
        (512 : ℤ) • (X ^ 17 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 17) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284177.main) := by
  intro h
  exact coefficient_contradiction a (h.2 17 (by decide)) h.1
