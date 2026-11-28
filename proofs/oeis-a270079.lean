import OMAStatements.S_oeis_a270079

open OMA.S_oeis_a270079 PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a270079.main) := by
  intro h
  have hr := h.1 12 (by decide)
  have hg := h.2
  have hs :
      (1 : ℤ) • (PowerSeries.mk a * (X ^ 0 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 1 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 2 : PowerSeries ℤ)) +
        (1 : ℤ) • (PowerSeries.mk a * (X ^ 3 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 4 : PowerSeries ℤ)) +
        (1 : ℤ) • (PowerSeries.mk a * (X ^ 5 : PowerSeries ℤ)) +
        (1 : ℤ) • (PowerSeries.mk a * (X ^ 6 : PowerSeries ℤ)) +
        (-1 : ℤ) • (PowerSeries.mk a * (X ^ 7 : PowerSeries ℤ)) =
      (1 : ℤ) • (X ^ 0 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 1 : PowerSeries ℤ) +
        (6 : ℤ) • (X ^ 2 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 3 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 4 : PowerSeries ℤ) +
        (6 : ℤ) • (X ^ 6 : PowerSeries ℤ) +
        (-12 : ℤ) • (X ^ 7 : PowerSeries ℤ) +
        (-1 : ℤ) • (X ^ 8 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 9 : PowerSeries ℤ) +
        (4 : ℤ) • (X ^ 10 : PowerSeries ℤ) +
        (-4 : ℤ) • (X ^ 12 : PowerSeries ℤ) := by
    simp only [zsmul_eq_mul]
    linear_combination hg
  have hc := congrArg (PowerSeries.coeff (R := ℤ) 12) hs
  simp only [map_add, map_zsmul, coeff_mul_X_pow', coeff_X_pow, coeff_mk] at hc
  norm_num [zsmul_eq_mul] at hc hr
  omega
