import OMAStatements.S_oeis_a287190

open OMA.S_oeis_a287190 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      1 + 10 * X - 101 * X ^ 2 + 100 * X ^ 3 + 111 * X ^ 4 - 1100 * X ^ 6)
    (hrule : ∀ n : ℕ, 4 < n → a n = 101 * a (n - 2) - 100 * a (n - 4)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-101 : ℤ) • (mk a * X ^ 2)
      + (100 : ℤ) • (mk a * X ^ 4) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (10 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (-101 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (100 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (111 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (-1100 : ℤ) • (X ^ 6 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 6) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 6 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a287190.main) := by
  intro h
  exact coefficient_contradiction a h.1 h.2.2.2
