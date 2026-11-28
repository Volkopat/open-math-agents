import OMAStatements.S_oeis_a282411

section Disproof_a282411
open PowerSeries

lemma coeff_mul_sub (f : PowerSeries ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (f * (1 - C c * X ^ k)) =
      coeff n f - c * (if k ≤ n then coeff (n - k) f else 0) := by
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm f (C c), mul_assoc,
      coeff_C_mul, coeff_mul_X_pow']

lemma coeff_C_X_pow (c : ℤ) (k n : ℕ) :
    coeff n (C c * X ^ k) = if n = k then c else 0 := by
  rw [coeff_C_mul, coeff_X_pow]; split_ifs <;> simp

end Disproof_a282411

open PowerSeries in
set_option maxHeartbeats 2000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282411.main) := by
  rintro ⟨_, hrec, hgf, _⟩
  have h5 := hrec 5 (by decide)
  let s := PowerSeries.mk (fun n => (OMA.S_oeis_a282411.a n : ℤ))
  have hlhs : s * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      s * (1 - C 1 * X ^ 2) * (1 - C 100 * X ^ 2) := by
    simp only [map_one, map_ofNat]; ring
  have hrhs : (1 + X + 10 * X ^ 2 - 101 * X ^ 3 + 100 * X ^ 5 : PowerSeries ℤ) =
      1 + C 1 * X ^ 1 + C 10 * X ^ 2 - C 101 * X ^ 3 + C 100 * X ^ 5 := by
    simp only [map_one, map_ofNat, pow_one, one_mul]
  have hc := congr_arg (PowerSeries.coeff 5) ((hlhs.symm.trans hgf).trans hrhs)
  simp only [coeff_mul_sub, s, coeff_mk] at hc
  simp only [map_add, map_sub, coeff_one, coeff_C_X_pow] at hc
  norm_num at hc h5
  linarith
