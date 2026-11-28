import OMAStatements.S_oeis_a289873
import Mathlib

open OMA.S_oeis_a289873 PowerSeries

lemma OMA.six (k : ℕ) : a (k + 6) = a k + 4 * (k : ℚ) + 12 := by
  simp only [a, show (k + 6) % 6 = k % 6 by omega]
  push_cast
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a289873.main := by
  have e : ((1 - X) ^ 3 * (1 + X) * (1 - X + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℚ) =
      1 - C 2 * X ^ 1 + X ^ 2 - X ^ 6 + C 2 * X ^ 7 - X ^ 8 := by
    simp only [map_ofNat]; ring
  have r : (X ^ 2 * (1 + X - X ^ 2) * (1 + X ^ 2 - X ^ 3 + 2 * X ^ 4 + X ^ 5) : PowerSeries ℚ) =
      X ^ 2 + X ^ 3 + C 4 * X ^ 7 - X ^ 8 - X ^ 9 := by
    simp only [map_ofNat]; ring
  rw [e, r]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mk]
  rw [mul_comm (mk _) (C 2 * X ^ 1), mul_comm (mk _) (X ^ 2), mul_comm (mk _) (X ^ 6),
    mul_comm (mk _) (C 2 * X ^ 7), mul_comm (mk _) (X ^ 8), mul_assoc, mul_assoc,
    coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul', coeff_X_pow_mul',
    coeff_X_pow_mul', coeff_X_pow_mul']
  simp only [coeff_C_mul, coeff_X_pow, coeff_mk]
  rcases Nat.lt_or_ge n 10 with h | h
  · interval_cases n <;> norm_num [a]
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 6 ≤ n by omega), if_pos (show 7 ≤ n by omega), if_pos (show 8 ≤ n by omega),
      if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega), if_neg (show n ≠ 9 by omega)]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    rw [show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega,
      show k + 10 - 6 = k + 4 by omega, show k + 10 - 7 = k + 3 by omega,
      show k + 10 - 8 = k + 2 by omega]
    simp only [if_neg (show ¬ k + 10 < 2 by omega), if_neg (show ¬ k + 9 < 2 by omega),
      if_neg (show ¬ k + 8 < 2 by omega), if_neg (show ¬ k + 4 < 2 by omega),
      if_neg (show ¬ k + 3 < 2 by omega), if_neg (show ¬ k + 2 < 2 by omega)]
    rw [show k + 10 = (k + 4) + 6 by ring, show k + 9 = (k + 3) + 6 by ring,
      show k + 8 = (k + 2) + 6 by ring, OMA.six, OMA.six, OMA.six]
    push_cast
    ring
