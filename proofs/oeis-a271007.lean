import OMAStatements.S_oeis_a271007

open OMA.S_oeis_a271007 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 10 = (-a (10 - 1)) + 2 * a (10 - 2) + 2 * a (10 - 3) - a (10 - 4) - a (10 - 5))
    (hg : PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X) ^ 3) =
      (7 + 3 * X + 22 * X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 - 3 * X ^ 5 - 4 * X ^ 6 - 3 * X ^ 7
       + 8 * X ^ 8 - 4 * X ^ 10 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (1 : ℤ) • (PowerSeries.mk a * (X ^ 1 : PowerSeries ℤ)) +
        (-2 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (-2 : ℤ) • (PowerSeries.mk a * (X ^ 3 : PowerSeries ℤ)) +
        (1 : ℤ) • (PowerSeries.mk a * (X ^ 4 : PowerSeries ℤ)) +
        (1 : ℤ) • (PowerSeries.mk a * (X ^ 5 : PowerSeries ℤ)) =
      (7 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (3 : ℤ) • (X ^ 1 : PowerSeries ℤ) +
        (22 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (3 : ℤ) • (X ^ 3 : PowerSeries ℤ) +
        (3 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (-3 : ℤ) • (X ^ 5 : PowerSeries ℤ) +
        (-4 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (-3 : ℤ) • (X ^ 7 : PowerSeries ℤ) +
        (8 : ℤ) • (X ^ 8 : PowerSeries ℤ) +
        (-4 : ℤ) • (X ^ 10 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 10) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a271007.main) := by
  intro h
  exact coefficient_contradiction a (h.2.2.2.1 10 (by decide)) h.2.2.2.2
