import OMAStatements.S_oeis_a154806
import Mathlib

namespace OMA.S_oeis_a154806

open PowerSeries

private theorem base : a 4 0 = 0 := rfl

private theorem step (n : ℕ) :
    a 4 (n + 1) = 16 * a 4 n + (if n % 2 = 0 then 15 else 0) := by
  unfold a
  rw [digits, Nat.ofDigits_append]
  simp only [List.length_replicate, Nat.cast_add, Nat.cast_mul]
  by_cases h : n % 2 = 0
  · have hblock : Nat.ofDigits 2 (List.replicate 4 1) = 15 := by decide +kernel
    norm_num [h, hblock]
    ring
  · norm_num [h, Nat.ofDigits_replicate_zero]

private theorem alternating (n : ℕ) :
    (-1 : ℤ) ^ n = if n % 2 = 0 then 1 else -1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ, ih]
    by_cases h : n % 2 = 0
    · rw [if_pos h, if_neg (show (n + 1) % 2 ≠ 0 by omega)]
      norm_num
    · rw [if_neg h, if_pos (show (n + 1) % 2 = 0 by omega)]
      norm_num

private theorem explicit (n : ℕ) :
    34 * a 4 n = 2 * (2 : ℤ) ^ (4 * n + 4) - 15 * (-1 : ℤ) ^ n - 17 := by
  induction n with
  | zero => norm_num [base]
  | succ n ih =>
    have hpow : (2 : ℤ) ^ (4 * (n + 1) + 4) = 16 * (2 : ℤ) ^ (4 * n + 4) := by
      rw [show 4 * (n + 1) + 4 = (4 * n + 4) + 4 by omega, pow_add]
      norm_num
      ring
    rw [step, hpow, pow_succ (-1 : ℤ)]
    by_cases h : n % 2 = 0
    · rw [alternating, if_pos h]
      rw [alternating, if_pos h] at ih
      norm_num [h]
      linarith only [ih]
    · rw [alternating, if_neg h]
      rw [alternating, if_neg h] at ih
      norm_num [h]
      linarith only [ih]

private def pulse (n : ℕ) : ℤ := if n % 2 = 1 then 15 else 0

private theorem series_step :
    mk (a 4) * (1 - X ^ 1 * C (16 : ℤ)) = mk pulse := by
  ext n
  simp only [mul_sub, mul_one, ← mul_assoc, map_sub, coeff_mul_C, coeff_mul_X_pow', coeff_mk]
  cases n with
  | zero => norm_num [base, pulse]
  | succ n =>
    have h : (n + 1) % 2 = 1 ↔ n % 2 = 0 := by omega
    simp only [if_pos (show 1 ≤ n + 1 by omega), Nat.add_sub_cancel, pulse, h, step]
    ring

private theorem pulse_series : mk pulse * (1 - X ^ 2) = X ^ 1 * C (15 : ℤ) := by
  ext n
  simp only [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_mk, coeff_mul_C, coeff_X_pow]
  by_cases h : 2 ≤ n
  · have hm : (n - 2) % 2 = n % 2 := by omega
    simp [h, pulse, hm, show n ≠ 1 by omega]
  · interval_cases n <;> norm_num [pulse]

private theorem generating :
    (1 - X ^ 2) * (1 - C (16 : ℤ) * X) * mk (a 4) = C (15 : ℤ) * X ^ 1 := by
  calc
    _ = (mk (a 4) * (1 - X ^ 1 * C (16 : ℤ))) * (1 - X ^ 2) := by
      simp only [pow_one]
      ring
    _ = _ := by
      rw [series_step, pulse_series, mul_comm]

end OMA.S_oeis_a154806

open OMA.S_oeis_a154806 in
theorem OMA.solution : type_of% @OMA.S_oeis_a154806.main := by
  exact ⟨fun n _ => explicit n, generating⟩