import OMAStatements.S_oeis_a020964
import Mathlib

/-!
Terms with exponent at most -2 vanish, so a(0) = 1 and a(n+1) = a(n) + floor(3(1+√2)^n).
With Q_k = (1+√2)^k + (1-√2)^k, floor(3(1+√2)^k) = 3 Q_k - (1+(-1)^k)/2 for k ≥ 2,
which gives the recurrence and, with the first values, the generating function.
-/

namespace R020964
open OMA.S_oeis_a020964 PowerSeries

def Q : ℕ → ℤ
  | 0 => 2
  | 1 => 2
  | m + 2 => 2 * Q (m + 1) + Q m

theorem hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem hs1 : 7 / 5 < √2 ∧ √2 < 3 / 2 := by
  constructor <;> nlinarith [hs, Real.sqrt_nonneg 2]

theorem Qr : ∀ m, (Q m : ℝ) = (1 + √2) ^ m + (1 - √2) ^ m
  | 0 => by simp only [Q]; push_cast; ring
  | 1 => by simp only [Q]; push_cast; ring
  | m + 2 => by
    simp only [Q]; push_cast; rw [Qr m, Qr (m + 1)]
    linear_combination (-(1 + √2) ^ m - (1 - √2) ^ m) * hs

theorem bb (j : ℕ) : 0 < (√2 - 1) ^ (j + 2) ∧ 3 * (√2 - 1) ^ (j + 2) < 1 := by
  obtain ⟨h1, h2⟩ := hs1
  have := pow_le_pow_of_le_one (by linarith : (0 : ℝ) ≤ √2 - 1) (by linarith)
    (show 2 ≤ j + 2 by omega)
  exact ⟨pow_pos (by linarith) _, by nlinarith [hs]⟩

theorem fl (k : ℕ) (hk : 2 ≤ k) :
    (⌊3 * (1 + √2) ^ k⌋ : ℝ) = 3 * Q k - (1 + (-1) ^ k) / 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have e : (1 - √2) ^ (j + 2) = (-1) ^ (j + 2) * (√2 - 1) ^ (j + 2) := by
    rw [← mul_pow]; ring
  obtain ⟨b0, b1⟩ := bb j
  have q := Qr (j + 2)
  rcases neg_one_pow_eq_or ℝ (j + 2) with h | h <;> rw [h] at e ⊢
  · have : ⌊3 * (1 + √2) ^ (j + 2)⌋ = 3 * Q (j + 2) - 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; push_cast; ring
  · have : ⌊3 * (1 + √2) ^ (j + 2)⌋ = 3 * Q (j + 2) := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [this]; push_cast; ring

theorem inv_al : (1 + √2)⁻¹ = √2 - 1 := inv_eq_of_mul_eq_one_right (by linear_combination hs)

theorem a_fin (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n + 1), ⌊3 * (1 + √2) ^ ((n : ℤ) - ((k : ℤ) + 1))⌋ := by
  rw [a]
  refine tsum_eq_sum fun k hk => ?_
  simp only [Finset.mem_range, not_lt] at hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show (n : ℤ) - (((n + 1 + j : ℕ) : ℤ) + 1) = -((j + 2 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, ← inv_pow, inv_al, Int.floor_eq_zero_iff]
  obtain ⟨b0, b1⟩ := bb j
  exact ⟨by linarith, b1⟩

theorem a_succ (n : ℕ) : a (n + 1) = a n + ⌊3 * (1 + √2) ^ n⌋ := by
  rw [a_fin (n + 1), Finset.sum_range_succ', a_fin n]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, add_sub_cancel_right,
    add_sub_add_right_eq_sub, zpow_natCast]

theorem a_zero : a 0 = 1 := by
  rw [a_fin]
  simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, zero_sub, zpow_neg_one, inv_al]
  rw [Int.floor_eq_iff]
  obtain ⟨h1, h2⟩ := hs1
  constructor <;> push_cast <;> linarith

theorem rec (m : ℕ) : a (m + 7) = 3 * a (m + 6) - 4 * a (m + 4) + a (m + 3) + a (m + 2) := by
  have h3 : a (m + 3) = a (m + 2) + ⌊3 * (1 + √2) ^ (m + 2)⌋ := a_succ _
  have h4 : a (m + 4) = a (m + 3) + ⌊3 * (1 + √2) ^ (m + 3)⌋ := a_succ _
  have h5 : a (m + 5) = a (m + 4) + ⌊3 * (1 + √2) ^ (m + 4)⌋ := a_succ _
  have h6 : a (m + 6) = a (m + 5) + ⌊3 * (1 + √2) ^ (m + 5)⌋ := a_succ _
  have h7 : a (m + 7) = a (m + 6) + ⌊3 * (1 + √2) ^ (m + 6)⌋ := a_succ _
  have key : (⌊3 * (1 + √2) ^ (m + 6)⌋ - 2 * ⌊3 * (1 + √2) ^ (m + 5)⌋
      - 2 * ⌊3 * (1 + √2) ^ (m + 4)⌋ + 2 * ⌊3 * (1 + √2) ^ (m + 3)⌋
      + ⌊3 * (1 + √2) ^ (m + 2)⌋ : ℝ) = 0 := by
    rw [fl (m + 6) (by omega), fl (m + 5) (by omega), fl (m + 4) (by omega),
      fl (m + 3) (by omega), fl (m + 2) (by omega)]
    simp only [Qr]
    linear_combination (3 * (1 + √2) ^ (m + 2) * ((1 + √2) ^ 2 - 1)
      + 3 * (1 - √2) ^ (m + 2) * ((1 - √2) ^ 2 - 1)) * hs
  have key' : ⌊3 * (1 + √2) ^ (m + 6)⌋ - 2 * ⌊3 * (1 + √2) ^ (m + 5)⌋
      - 2 * ⌊3 * (1 + √2) ^ (m + 4)⌋ + 2 * ⌊3 * (1 + √2) ^ (m + 3)⌋
      + ⌊3 * (1 + √2) ^ (m + 2)⌋ = 0 := by exact_mod_cast key
  linear_combination h7 - 2 * h6 - 2 * h5 + 2 * h4 + h3 + key'

theorem vals : a 1 = 4 ∧ a 2 = 11 ∧ a 3 = 28 ∧ a 4 = 70 ∧ a 5 = 171 ∧ a 6 = 417 := by
  obtain ⟨h1, h2⟩ := hs1
  have e : ∀ k (q r : ℤ), 2 ≤ k → Q k = q → (3 * q - (1 + (-1) ^ k) / 2 : ℝ) = r →
      ⌊3 * (1 + √2) ^ k⌋ = r := fun k q r hk hq hr => by
    subst hq; exact Int.cast_inj.1 ((fl k hk).trans hr)
  have a1 : a 1 = a 0 + ⌊3 * (1 + √2) ^ 0⌋ := a_succ 0
  have a2 : a 2 = a 1 + ⌊3 * (1 + √2) ^ 1⌋ := a_succ 1
  have a3 : a 3 = a 2 + ⌊3 * (1 + √2) ^ 2⌋ := a_succ 2
  have a4 : a 4 = a 3 + ⌊3 * (1 + √2) ^ 3⌋ := a_succ 3
  have a5 : a 5 = a 4 + ⌊3 * (1 + √2) ^ 4⌋ := a_succ 4
  have a6 : a 6 = a 5 + ⌊3 * (1 + √2) ^ 5⌋ := a_succ 5
  have e1 : ⌊3 * (1 + √2) ^ 1⌋ = 7 := by
    rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  rw [e 2 6 17 (by norm_num) rfl (by norm_num)] at a3
  rw [e 3 14 42 (by norm_num) rfl (by norm_num)] at a4
  rw [e 4 34 101 (by norm_num) rfl (by norm_num)] at a5
  rw [e 5 82 246 (by norm_num) rfl (by norm_num)] at a6
  rw [pow_zero, mul_one, Int.floor_ofNat, a_zero] at a1
  omega

theorem inv_lem {f N D : ℤ⟦X⟧} (h : constantCoeff D = 1) (h2 : f * D = N) :
    f = invOfUnit D 1 * N := by
  rw [← h2, mul_comm (invOfUnit D 1), mul_assoc, mul_invOfUnit D 1 (by rw [h, Units.val_one]),
    mul_one]

end R020964

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a020964.main := by
  open OMA.S_oeis_a020964 R020964 in
  refine ⟨fun n hn => ?_, inv_lem (by simp) ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 3 = m + 4 by omega,
      show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega]
    exact rec m
  · obtain ⟨v1, v2, v3, v4, v5, v6⟩ := vals
    rw [show ∀ p : ℤ⟦X⟧, p * (1 - C 3 * X + C 4 * X ^ 3 - X ^ 4 - X ^ 5)
        = p - C 3 * (p * X ^ 1) + C 4 * (p * X ^ 3) - p * X ^ 4 - p * X ^ 5 from
        fun p => by ring]
    ext n
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_one, coeff_X,
      coeff_X_pow]
    rcases Nat.lt_or_ge n 7 with h | h
    · rcases n with _ | _ | _ | _ | _ | _ | _ | n
      all_goals first | omega | simp [a_zero, v1, v2, v3, v4, v5, v6]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      simp
      linarith [rec m]
