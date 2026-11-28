import OMAStatements.S_oeis_a279498

open OMA.S_oeis_a279498 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 10 = a (10 - 2) + 10000 * a (10 - 4) - 10000 * a (10 - 6))
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2)) =
      (1 + 100 * X ^ 2 + 10 * X ^ 4 + 990 * X ^ 6 - 1000 * X ^ 10 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (-10000 : ℤ) • (PowerSeries.mk a * (X ^ 4 : PowerSeries ℤ)) +
        (10000 : ℤ) • (PowerSeries.mk a * (X ^ 6 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (100 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (10 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (990 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (-1000 : ℤ) • (X ^ 10 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 10) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279498.main) := by
  intro h
  exact coefficient_contradiction a (h.1 10 (by decide)) h.2
