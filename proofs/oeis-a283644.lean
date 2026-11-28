import OMAStatements.S_oeis_a283644

open OMA.S_oeis_a283644 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + X ^ 2) * (1 + X ^ 4)) =
      1 + X + X ^ 2 - 99 * X ^ 3 + X ^ 4 - 99 * X ^ 5 - 9999 * X ^ 6 + 1009901 * X ^ 7 - 100 * X ^ 9 -
      10000 * X ^ 10 + 1010000 * X ^ 11 - 100000000 * X ^ 12)
    (h0 : a 0 = 1)
    (h1 : a 1 = 11)
    (h2 : a 2 = 101) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-10 : ℤ) • (mk a * X ^ 1)
      + (-1 : ℤ) • (mk a * X ^ 8)
      + (10 : ℤ) • (mk a * X ^ 9) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (-99 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (-99 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (-9999 : ℤ) • (X ^ 6 : PowerSeries ℤ)
      + (1009901 : ℤ) • (X ^ 7 : PowerSeries ℤ)
      + (-100 : ℤ) • (X ^ 9 : PowerSeries ℤ)
      + (-10000 : ℤ) • (X ^ 10 : PowerSeries ℤ)
      + (1010000 : ℤ) • (X ^ 11 : PowerSeries ℤ)
      + (-100000000 : ℤ) • (X ^ 12 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 2) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc

  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283644.main) := by
  intro h
  exact coefficient_contradiction a h.1 (by decide) (by decide) (by decide)
