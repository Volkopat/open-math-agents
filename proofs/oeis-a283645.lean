import OMAStatements.S_oeis_a283645

open OMA.S_oeis_a283645 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + X ^ 2) * (1 + X ^ 4)) =
      1 + 11 * X + X ^ 2 - 89 * X ^ 3 + X ^ 4 - 89 * X ^ 5 + 1001 * X ^ 6 + 8911 * X ^ 7 - 100 * X ^ 9 +
      1000 * X ^ 10 + 9000 * X ^ 11 + 10000000 * X ^ 15)
    (hrule : ∀ n : ℕ, 11 < n → a n = 100 * a (n - 2) + a (n - 8) - 100 * a (n - 10)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-100 : ℤ) • (mk a * X ^ 2)
      + (-1 : ℤ) • (mk a * X ^ 8)
      + (100 : ℤ) • (mk a * X ^ 10) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (11 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (-89 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (-89 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (1001 : ℤ) • (X ^ 6 : PowerSeries ℤ)
      + (8911 : ℤ) • (X ^ 7 : PowerSeries ℤ)
      + (-100 : ℤ) • (X ^ 9 : PowerSeries ℤ)
      + (1000 : ℤ) • (X ^ 10 : PowerSeries ℤ)
      + (9000 : ℤ) • (X ^ 11 : PowerSeries ℤ)
      + (10000000 : ℤ) • (X ^ 15 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 15) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 15 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283645.main) := by
  intro h
  exact coefficient_contradiction a h.1 h.2
