import OMAStatements.S_oeis_a279878

open OMA.S_oeis_a279878 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 8 = 111 * a (8 - 2) - 1110 * a (8 - 4) + 1000 * a (8 - 6))
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      (1 + X - 101 * X ^ 2 - 100 * X ^ 3 + 11100 * X ^ 4 - 111000 * X ^ 6 + 100000 * X ^ 8 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-111 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (1110 : ℤ) • (PowerSeries.mk a * (X ^ 4 : PowerSeries ℤ)) +
        (-1000 : ℤ) • (PowerSeries.mk a * (X ^ 6 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (1 : ℤ) • (X ^ 1 : PowerSeries ℤ) +
        (-101 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (-100 : ℤ) • (X ^ 3 : PowerSeries ℤ) +
        (11100 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (-111000 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (100000 : ℤ) • (X ^ 8 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 8) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279878.main) := by
  intro h
  exact coefficient_contradiction a (h.1 8 (by decide)) h.2
