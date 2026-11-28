import OMAStatements.S_oeis_a279874

open OMA.S_oeis_a279874 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + X ^ 2)) =
      1 + 10 * X + X ^ 2 + 110 * X ^ 3 - 10100 * X ^ 4 + 10000 * X ^ 6 - 990000 * X ^ 7 + 99000000 * X ^
      8 + 100000000 * X ^ 9 - 10000000000 * X ^ 10 - 100000000 * X ^ 12 + 10000000000 * X ^ 14)
    (hrule : ∀ n : ℕ, 10 < n → a n = 100 * a (n - 2) + a (n - 4) - 100 * a (n - 6)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-100 : ℤ) • (mk a * X ^ 2)
      + (-1 : ℤ) • (mk a * X ^ 4)
      + (100 : ℤ) • (mk a * X ^ 6) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (10 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (110 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (-10100 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (10000 : ℤ) • (X ^ 6 : PowerSeries ℤ)
      + (-990000 : ℤ) • (X ^ 7 : PowerSeries ℤ)
      + (99000000 : ℤ) • (X ^ 8 : PowerSeries ℤ)
      + (100000000 : ℤ) • (X ^ 9 : PowerSeries ℤ)
      + (-10000000000 : ℤ) • (X ^ 10 : PowerSeries ℤ)
      + (-100000000 : ℤ) • (X ^ 12 : PowerSeries ℤ)
      + (10000000000 : ℤ) • (X ^ 14 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 12) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 12 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279874.main) := by
  intro h
  exact coefficient_contradiction a h.2 h.1
