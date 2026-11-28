import OMAStatements.S_oeis_a290413

section Disproof_a290413
open PowerSeries

lemma coeff_mul_sub (f : PowerSeries ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (f * (1 - C c * X ^ k)) =
      coeff n f - c * (if k ≤ n then coeff (n - k) f else 0) := by
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm f (C c), mul_assoc,
      coeff_C_mul, coeff_mul_X_pow']

lemma coeff_C_X_pow (c : ℤ) (k n : ℕ) :
    coeff n (C c * X ^ k) = if n = k then c else 0 := by
  rw [coeff_C_mul, coeff_X_pow]; split_ifs <;> simp

end Disproof_a290413

open PowerSeries in
set_option maxHeartbeats 2000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a290413.main) := by
  rintro ⟨hgf, hrec⟩
  have h8 := hrec 8 (by decide)
  let s := PowerSeries.mk (fun n => (OMA.S_oeis_a290413.a n : ℤ))
  have hp1 : (1 - 10 * X) * (1 + 10 * X : PowerSeries ℤ) = 1 - C 100 * X ^ 2 := by
    simp only [map_ofNat]; ring
  have hlhs : s * ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      s * (1 - C 1 * X ^ 1) * (1 - C 100 * X ^ 2) * (1 - C 10 * X ^ 2) := by
    have hmul : (1 - X) * (1 - 10 * X) * (1 + 10 * X : PowerSeries ℤ) =
        (1 - C 1 * X ^ 1) * (1 - C 100 * X ^ 2) := by
      rw [mul_assoc, hp1]; simp only [map_one, one_mul, pow_one]
    rw [hmul, show (1 - 10 * X ^ 2 : PowerSeries ℤ) = 1 - C 10 * X ^ 2 by simp only [map_ofNat]]
    simp only [mul_assoc]
  have hrhs : (1 - 10 * X ^ 2 + 10 * X ^ 3 - 100 * X ^ 4 + 100000 * X ^ 5 - 1100000 * X ^ 6 +
      11000000 * X ^ 8 - 10000000 * X ^ 9 : PowerSeries ℤ) =
      1 - C 10 * X ^ 2 + C 10 * X ^ 3 - C 100 * X ^ 4 + C 100000 * X ^ 5 -
      C 1100000 * X ^ 6 + C 11000000 * X ^ 8 - C 10000000 * X ^ 9 := by
    simp only [map_ofNat]
  have hc := congr_arg (PowerSeries.coeff 8) ((hlhs.symm.trans hgf).trans hrhs)
  simp only [coeff_mul_sub, s, coeff_mk] at hc
  simp only [map_add, map_sub, coeff_one, coeff_C_X_pow] at hc
  norm_num at hc h8
  linarith
