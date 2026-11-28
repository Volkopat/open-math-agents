import OMAStatements.S_oeis_a269782

open OMA.S_oeis_a269782 PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a269782.main) := by
  intro h
  have hg := h.2.2.2.2
  have hp : (1 : ℤ) • (mk a * X ^ 0)
      + (-3 : ℤ) • (mk a * X ^ 2)
      + (3 : ℤ) • (mk a * X ^ 4)
      + (-1 : ℤ) • (mk a * X ^ 6) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 1 : PowerSeries ℤ)
      + (2 : ℤ) • (X ^ 2 : PowerSeries ℤ)
      + (24 : ℤ) • (X ^ 3 : PowerSeries ℤ)
      + (-3 : ℤ) • (X ^ 4 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 6 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 7 : PowerSeries ℤ)
      + (-8 : ℤ) • (X ^ 8 : PowerSeries ℤ)
      + (4 : ℤ) • (X ^ 10 : PowerSeries ℤ) := by
    convert hg using 1 <;> simp only [zsmul_eq_mul] <;> push_cast <;> ring
  have hc := congrArg (coeff (R := ℤ) 10) hp
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc
  have hr := h.2.2.2.1 10 (by decide)
  norm_num only [Nat.reduceSub, Nat.reduceMod, Nat.cast_ofNat] at hr
  linarith
