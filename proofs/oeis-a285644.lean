import OMAStatements.S_oeis_a285644

open OMA.S_oeis_a285644 PowerSeries

lemma coefficient_contradiction (a : ℕ → ℤ)
    (hg : PowerSeries.mk a * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      1 + X - X ^ 2 - 90 * X ^ 3 + 100 * X ^ 5 + 100000 * X ^ 6 - 100000 * X ^ 8)
    (hrule : ∀ n : ℕ, 3 < n → a n = 101 * a (n - 2) - 100 * a (n - 4)) : False := by
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-101 : ℤ) • (mk a * X ^ 2)
      + (100 : ℤ) • (mk a * X ^ 4) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (1 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (-1 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (-90 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (100 : ℤ) • (X ^ 5 : PowerSeries ℤ)
      + (100000 : ℤ) • (X ^ 6 : PowerSeries ℤ)
      + (-100000 : ℤ) • (X ^ 8 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 5) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := hrule 5 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a285644.main) := by
  intro h
  exact coefficient_contradiction a h.1 h.2.2.2
