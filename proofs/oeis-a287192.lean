import OMAStatements.S_oeis_a287192

open PowerSeries

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a287192.main) := by
  rintro ⟨hgf, _, _, hrec⟩
  have h6 := hrec 6 (by decide)
  let s := PowerSeries.mk (fun n => (OMA.S_oeis_a287192.a n : ℤ))
  have heq : C (1 : ℤ) * (s * X ^ 0) + C (-5 : ℤ) * (s * X ^ 2) + C (4 : ℤ) * (s * X ^ 4) =
      C (1 : ℤ) * X ^ 0 + C (2 : ℤ) * X ^ 1 + C (-5 : ℤ) * X ^ 2 +
      C (4 : ℤ) * X ^ 3 + C (7 : ℤ) * X ^ 4 + C (-12 : ℤ) * X ^ 6 := by
    calc C (1 : ℤ) * (s * X ^ 0) + C (-5 : ℤ) * (s * X ^ 2) + C (4 : ℤ) * (s * X ^ 4)
      _ = s * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) := by
        simp only [map_neg, map_one, map_ofNat]; ring
      _ = 1 + 2 * X - 5 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 12 * X ^ 6 := hgf
      _ = _ := by simp only [map_neg, map_one, map_ofNat]; ring
  have hc := congr_arg (PowerSeries.coeff 6) heq
  simp only [map_add, coeff_C_mul] at hc
  simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk] at hc
  norm_num at hc h6
  linarith
