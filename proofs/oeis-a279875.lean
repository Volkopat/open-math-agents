import OMAStatements.S_oeis_a279875

open OMA.S_oeis_a279875 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2)) =
      1 + X + 4 * X ^ 2 + 6 * X ^ 3 - 5 * X ^ 4 + 4 * X ^ 6 + 6 * X ^ 7 - 3 * X ^ 8 + 2 * X ^ 9 - X ^ 10
      - 16 * X ^ 12 + 16 * X ^ 14)
    (hrule : ∀ n : ℕ, 10 < n → a n = a (n - 2) + 16 * a (n - 4) - 16 * a (n - 6)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-1 : ℤ) • (mk a * X ^ 2)
      + (-16 : ℤ) • (mk a * X ^ 4)
      + (16 : ℤ) • (mk a * X ^ 6) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (6 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (-5 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 6 : PowerSeries ℤ)
      + (6 : ℤ) • (X ^ 7 : PowerSeries ℤ)
      + (-3 : ℤ) • (X ^ 8 : PowerSeries ℤ)
      + (2 : ℤ) • (X ^ 9 : PowerSeries ℤ)
      + (-1 : ℤ) • (X ^ 10 : PowerSeries ℤ)
      + (-16 : ℤ) • (X ^ 12 : PowerSeries ℤ)
      + (16 : ℤ) • (X ^ 14 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 12) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 12 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279875.main) := by
  intro h
  exact coefficient_contradiction a h.2 h.1
