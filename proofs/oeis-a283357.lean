import OMAStatements.S_oeis_a283357

open OMA.S_oeis_a283357 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + X - 2 * X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4 + X ^ 5 + 4 * X ^ 7)
    (hrule : ∀ n : ℕ, 5 < n → a n = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-1 : ℤ) • (mk a * X ^ 1)
      + (-4 : ℤ) • (mk a * X ^ 2)
      + (4 : ℤ) • (mk a * X ^ 3) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (-2 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (3 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (-2 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 7 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 7) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 7 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283357.main) := by
  intro h
  exact coefficient_contradiction a h.1 h.2.2
