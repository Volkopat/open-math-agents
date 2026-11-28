import OMAStatements.S_oeis_a270008

open OMA.S_oeis_a270008 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) ^ 4 * (1 + X) ^ 3) =
      1 + 8 * X - 3 * X ^ 2 + 25 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 - X ^ 6 + X ^ 7)
    (hrule : ∀ n : ℕ, 6 < n → a n = a (n - 1) + 3 * a (n - 2) - 3 * a (n - 3) - 3 * a (n - 4) + 3 * a (n - 5) + a (n
      - 6) - a (n - 7)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-1 : ℤ) • (mk a * X ^ 1)
      + (-3 : ℤ) • (mk a * X ^ 2)
      + (3 : ℤ) • (mk a * X ^ 3)
      + (3 : ℤ) • (mk a * X ^ 4)
      + (-3 : ℤ) • (mk a * X ^ 5)
      + (-1 : ℤ) • (mk a * X ^ 6)
      + (1 : ℤ) • (mk a * X ^ 7) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (8 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (-3 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (25 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (3 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (-2 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (-1 : ℤ) • (X ^ 6 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 7 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 7) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 7 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270008.main) := by
  intro h
  exact coefficient_contradiction a h.2.2.2.2 h.2.2.2.1
