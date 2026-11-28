import OMAStatements.S_oeis_a203164
import Mathlib

open OMA.S_oeis_a203164 PowerSeries

lemma OMA.one (n : ℕ) : products (n + 1) =
    ((products n).1 * digit n, (products n).2 * digit n + (products n).1) := rfl

lemma OMA.four (n : ℕ) : products (n + 4) =
    (24 * (products n).1, 24 * (products n).2 + 50 * (products n).1) := by
  rw [OMA.one (n + 3), OMA.one (n + 2), OMA.one (n + 1), OMA.one n]
  have hd : ∀ k, digit k = digit (k % 4) := by
    intro k; simp only [digit, Nat.mod_mod]
  rw [hd n, hd (n + 1), hd (n + 2), hd (n + 3)]
  have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases this with h | h | h | h <;>
  · rw [show (n + 1) % 4 = (n % 4 + 1) % 4 by omega, show (n + 2) % 4 = (n % 4 + 2) % 4 by omega,
      show (n + 3) % 4 = (n % 4 + 3) % 4 by omega, h]
    simp only [digit]
    norm_num
    constructor <;> ring

lemma OMA.rec (m : ℕ) : a (m + 8) = 48 * a (m + 4) - 576 * a m := by
  simp only [a]
  rw [show m + 8 = (m + 4) + 4 by ring, OMA.four (m + 4), OMA.four m]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a203164.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [show m + 8 - 4 = m + 4 by omega, show m + 8 - 8 = m by omega]
    exact OMA.rec m
  · have e : (1 - C 24 * X ^ 4 : PowerSeries ℤ) ^ 2 = 1 - C 48 * X ^ 4 + C 576 * X ^ 8 := by
      simp only [map_ofNat]; ring
    have r : (X^1 + C 5 * X^2 + C 14 * X^3 + C 50 * X^4 + C 176 * X^5 + C 80 * X^6 + C 64 * X^7 : PowerSeries ℤ) = C 1 * X ^ 1 + C 5 * X ^ 2 + C 14 * X ^ 3 + C 50 * X ^ 4 + C 176 * X ^ 5 + C 80 * X ^ 6 + C 64 * X ^ 7 := by simp
    rw [e, r]
    ext n
    simp only [sub_mul, add_mul, one_mul, map_sub, map_add, coeff_mk]
    rw [mul_assoc, mul_assoc, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul']
    simp only [coeff_C_mul, coeff_X_pow, coeff_mk]
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n <;> decide
    · rw [if_pos (by omega), if_pos (by omega)]
      simp only [if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
        if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega),
        if_neg (show n ≠ 6 by omega), if_neg (show n ≠ 7 by omega)]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      rw [show k + 8 - 4 = k + 4 by omega, show k + 8 - 8 = k by omega, OMA.rec]
      ring
