import OMAStatements.S_oeis_a282654

open OMA.S_oeis_a282654 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2)) =
      1 + X + 6 * X ^ 2 + 3 * X ^ 3 + 8 * X ^ 4 - 4 * X ^ 5 + 4 * X ^ 7 + 16 * X ^ 11)
    (hrule : ∀ n : ℕ, 5 < n → a n = a (n - 2) + 16 * a (n - 4) - 16 * a (n - 6)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-1 : ℤ) • (mk a * X ^ 2)
      + (-16 : ℤ) • (mk a * X ^ 4)
      + (16 : ℤ) • (mk a * X ^ 6) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (6 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (3 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (8 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (-4 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 7 : PowerSeries ℤ)
      + (16 : ℤ) • (X ^ 11 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 7) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 7 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282654.main) := by
  intro h
  exact coefficient_contradiction a h.2 h.1
