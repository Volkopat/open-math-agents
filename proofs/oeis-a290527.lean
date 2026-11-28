import OMAStatements.S_oeis_a290527

section Disproof_a290527
open PowerSeries

lemma coeff_mul_sub (f : PowerSeries ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (f * (1 - C c * X ^ k)) =
      coeff n f - c * (if k ≤ n then coeff (n - k) f else 0) := by
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm f (C c), mul_assoc,
      coeff_C_mul, coeff_mul_X_pow']

lemma coeff_mul_add (f : PowerSeries ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (f * (1 + C c * X ^ k)) =
      coeff n f + c * (if k ≤ n then coeff (n - k) f else 0) := by
  rw [mul_add, mul_one, map_add, ← mul_assoc, mul_comm f (C c), mul_assoc,
      coeff_C_mul, coeff_mul_X_pow']

lemma coeff_C_X_pow (c : ℤ) (k n : ℕ) :
    coeff n (C c * X ^ k) = if n = k then c else 0 := by
  rw [coeff_C_mul, coeff_X_pow]; split_ifs <;> simp

end Disproof_a290527

open PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a290527.main) := by
  rintro ⟨hgf, _, _, hrec⟩
  have h6 := hrec 6 (by decide)
  let s := PowerSeries.mk (fun n => (OMA.S_oeis_a290527.a n : ℤ))
  have hlhs : s * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 - 2 * X ^ 2)) =
      s * (1 - C 1 * X ^ 1) * (1 + C 1 * X ^ 1) * (1 - C 2 * X ^ 1) * (1 - C 2 * X ^ 2) := by
    simp only [map_one, map_ofNat, one_mul, pow_one, mul_assoc]
  have hrhs : (1 - 2 * X ^ 2 + 5 * X ^ 3 - 7 * X ^ 4 + 6 * X ^ 6 -
      4 * X ^ 7 : PowerSeries ℤ) =
      1 - C 2 * X ^ 2 + C 5 * X ^ 3 - C 7 * X ^ 4 + C 6 * X ^ 6 - C 4 * X ^ 7 := by
    simp only [map_one, map_ofNat]
  have hc := congr_arg (PowerSeries.coeff 6) ((hlhs.symm.trans hgf).trans hrhs)
  simp only [coeff_mul_sub, coeff_mul_add, s, coeff_mk] at hc
  simp only [map_add, map_sub, coeff_one, coeff_C_X_pow] at hc
  norm_num at hc h6
  linarith
