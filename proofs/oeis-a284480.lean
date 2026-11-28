import OMAStatements.S_oeis_a284480

open OMA.S_oeis_a284480 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + X ^ 2)) =
      1 + X - 9 * X ^ 2 + 101 * X ^ 3 - 10 * X ^ 4 + 100 * X ^ 5 - 1000 * X ^ 7 + 10000 * X ^ 8)
    (hrule : ∀ n : ℕ, 5 < n → a n = 10 * a (n - 1) + a (n - 4) - 10 * a (n - 5)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-10 : ℤ) • (mk a * X ^ 1)
      + (-1 : ℤ) • (mk a * X ^ 4)
      + (10 : ℤ) • (mk a * X ^ 5) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (-9 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (101 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (-10 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (100 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (-1000 : ℤ) • (X ^ 7 : PowerSeries ℤ)
      + (10000 : ℤ) • (X ^ 8 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 7) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 7 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a284480.main) := by
  intro h
  exact coefficient_contradiction a h.1 h.2
