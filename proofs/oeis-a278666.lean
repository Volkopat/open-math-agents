import OMAStatements.S_oeis_a278666

open OMA.S_oeis_a278666 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 10 = a (10 - 1) + 16 * a (10 - 4) - 16 * a (10 - 5))
    (hg : PowerSeries.mk a * ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2)) =
      (1 + 2 * X + 3 * X ^ 2 + 6 * X ^ 3 - 4 * X ^ 4 - 6 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7
       + 16 * X ^ 10 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 1 : PowerSeries ℤ)) +
        (-16 : ℤ) • (PowerSeries.mk a * (X ^ 4 : PowerSeries ℤ)) +
        (16 : ℤ) • (PowerSeries.mk a * (X ^ 5 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (2 : ℤ) • (X ^ 1 : PowerSeries ℤ) +
        (3 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (6 : ℤ) • (X ^ 3 : PowerSeries ℤ) +
        (-4 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (-6 : ℤ) • (X ^ 5 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (-2 : ℤ) • (X ^ 7 : PowerSeries ℤ) +
        (16 : ℤ) • (X ^ 10 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 10) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a278666.main) := by
  intro h
  exact coefficient_contradiction a (h.1 10 (by decide)) h.2
