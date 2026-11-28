import OMAStatements.S_oeis_a283358

open OMA.S_oeis_a283358 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X)) =
      1 - X - 2 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 - 16 * X ^ 5 + 32 * X ^ 7)
    (hrule : ∀ n : ℕ, 5 < n → a n = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-2 : ℤ) • (mk a * X ^ 1)
      + (-1 : ℤ) • (mk a * X ^ 2)
      + (2 : ℤ) • (mk a * X ^ 3) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (-1 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (-2 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (12 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (-8 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (-16 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (32 : ℤ) • (X ^ 7 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 7) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 7 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283358.main) := by
  intro h
  exact coefficient_contradiction a h.1 h.2.2.2
