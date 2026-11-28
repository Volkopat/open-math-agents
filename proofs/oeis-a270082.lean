import OMAStatements.S_oeis_a270082

open OMA.S_oeis_a270082 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hr : a 11 = ((a (11 - 2) + a (11 - 4)) - a (11 - 6)))
    (hg : PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2)) =
      (4 + 7 * X + 4 * X ^ 2 + 5 * X ^ 3 + 5 * X ^ 5 - 12 * X ^ 6 - X ^ 7 + 4 * X ^ 8 + 4 * X ^ 9 - 4 * X ^ 11 : PowerSeries ℤ)) : False := by
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 4 : PowerSeries ℤ)) +
        (1 : ℤ) • (PowerSeries.mk a * (X ^ 6 : PowerSeries ℤ)) =
      (4 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (7 : ℤ) • (X ^ 1 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (5 : ℤ) • (X ^ 3 : PowerSeries ℤ) +
        (5 : ℤ) • (X ^ 5 : PowerSeries ℤ) +
        (-12 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (-1 : ℤ) • (X ^ 7 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 8 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 9 : PowerSeries ℤ) +
        (-4 : ℤ) • (X ^ 11 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 11) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270082.main) := by
  intro h
  exact coefficient_contradiction a (h.1 11 (by decide)) h.2
