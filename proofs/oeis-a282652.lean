import OMAStatements.S_oeis_a282652

open OMA.S_oeis_a282652 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 + 100 * X ^ 2)) =
      1 + X + 110 * X ^ 2 + 99 * X ^ 3 + 1000 * X ^ 4 - 100 * X ^ 5 + 100 * X ^ 7 + 10000 * X ^ 11)
    (hrule : ∀ n : ℕ, 5 < n → a n = a (n - 2) + 10000 * a (n - 4) - 10000 * a (n - 6)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-1 : ℤ) • (mk a * X ^ 2)
      + (-10000 : ℤ) • (mk a * X ^ 4)
      + (10000 : ℤ) • (mk a * X ^ 6) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (110 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (99 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (1000 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (-100 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (100 : ℤ) • (X ^ 7 : PowerSeries ℤ)
      + (10000 : ℤ) • (X ^ 11 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 7) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 7 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282652.main) := by
  intro h
  exact coefficient_contradiction a h.2 h.1
