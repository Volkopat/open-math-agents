import OMAStatements.S_oeis_a283647

open OMA.S_oeis_a283647 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 + X ^ 2) * (1 + X ^ 4)) =
      1 + 3 * X + X ^ 2 - X ^ 3 + X ^ 4 - X ^ 5 + 9 * X ^ 6 + 7 * X ^ 7 - 4 * X ^ 9 + 8 * X ^ 10 + 8 * X
      ^ 11 + 128 * X ^ 15)
    (hrule : ∀ n : ℕ, 11 < n → a n = 4 * a (n - 2) + a (n - 8) - 4 * a (n - 10)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-4 : ℤ) • (mk a * X ^ 2)
      + (-1 : ℤ) • (mk a * X ^ 8)
      + (4 : ℤ) • (mk a * X ^ 10) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (3 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (-1 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (-1 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (9 : ℤ) • (X ^ 6 : PowerSeries ℤ)
      + (7 : ℤ) • (X ^ 7 : PowerSeries ℤ)
      + (-4 : ℤ) • (X ^ 9 : PowerSeries ℤ)
      + (8 : ℤ) • (X ^ 10 : PowerSeries ℤ)
      + (8 : ℤ) • (X ^ 11 : PowerSeries ℤ)
      + (128 : ℤ) • (X ^ 15 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 15) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 15 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a283647.main) := by
  intro h
  exact coefficient_contradiction a h.1 h.2
