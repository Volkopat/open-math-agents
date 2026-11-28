import OMAStatements.S_oeis_a004257
import Mathlib

namespace OMA.P004257

open OMA.S_oeis_a004257

lemma key (n : ℕ) (hn : 1 ≤ n) : a n = (Nat.log 2 (n ^ 2) : ℤ) - (Nat.log 2 n : ℤ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨m, hm⟩ : ∃ m, Nat.log 2 n = m := ⟨_, rfl⟩
  have hlo : 2 ^ m ≤ n := by
    rw [← hm]
    exact Nat.pow_log_le_self 2 hn0
  have hhi : n < 2 ^ (m + 1) := by
    rw [← hm]
    exact Nat.lt_pow_succ_log_self (by norm_num) n
  obtain ⟨x, hx⟩ : ∃ x, Real.logb 2 (n : ℝ) = x := ⟨_, rfl⟩
  have h2x : (2 : ℝ) ^ x = (n : ℝ) := by
    rw [← hx]
    exact Real.rpow_logb (by norm_num) (by norm_num) hnpos
  have h22x : (2 : ℝ) ^ (2 * x) = (n : ℝ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by norm_num), h2x]
    norm_cast
  have one_lt : (1 : ℝ) < 2 := by norm_num
  have hxm : (m : ℝ) ≤ x := by
    have h : (2 : ℝ) ^ (m : ℝ) ≤ (2 : ℝ) ^ x := by
      rw [h2x, Real.rpow_natCast]
      exact_mod_cast hlo
    exact (Real.rpow_le_rpow_left_iff one_lt).1 h
  have hxm1 : x < (m : ℝ) + 1 := by
    have h : (2 : ℝ) ^ x < (2 : ℝ) ^ ((m : ℝ) + 1) := by
      rw [h2x]
      have e : (2 : ℝ) ^ ((m : ℝ) + 1) = (2 : ℝ) ^ (m + 1) := by
        rw [← Real.rpow_natCast]
        push_cast
        rfl
      rw [e]
      exact_mod_cast hhi
    exact (Real.rpow_lt_rpow_left_iff one_lt).1 h
  have hsq_hi : n ^ 2 < 2 ^ (2 * m + 2) := by
    have h : n ^ 2 < (2 ^ (m + 1)) ^ 2 := Nat.pow_lt_pow_left hhi (by norm_num)
    have e : (2 ^ (m + 1)) ^ 2 = 2 ^ (2 * m + 2) := by ring
    rw [e] at h
    exact h
  have hsq_lo : 2 ^ (2 * m) ≤ n ^ 2 := by
    have h : (2 ^ m) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hlo 2
    have e : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by ring
    rw [e] at h
    exact h
  unfold a
  rw [hx, hm, round_eq]
  rcases Nat.lt_or_ge (n ^ 2) (2 ^ (2 * m + 1)) with hlt | hge
  · have hlog : Nat.log 2 (n ^ 2) = 2 * m := Nat.log_eq_of_pow_le_of_lt_pow hsq_lo hlt
    rw [hlog]
    have hx2 : 2 * x < 2 * (m : ℝ) + 1 := by
      have h : (2 : ℝ) ^ (2 * x) < (2 : ℝ) ^ (2 * (m : ℝ) + 1) := by
        rw [h22x]
        have e : (2 : ℝ) ^ (2 * (m : ℝ) + 1) = (2 : ℝ) ^ (2 * m + 1) := by
          rw [← Real.rpow_natCast]
          push_cast
          rfl
        rw [e]
        exact_mod_cast hlt
      exact (Real.rpow_lt_rpow_left_iff one_lt).1 h
    have hf : ⌊x + 1 / 2⌋ = (m : ℤ) := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    rw [hf]
    push_cast
    ring
  · have hlog : Nat.log 2 (n ^ 2) = 2 * m + 1 := Nat.log_eq_of_pow_le_of_lt_pow hge hsq_hi
    rw [hlog]
    have hx2 : 2 * (m : ℝ) + 1 ≤ 2 * x := by
      have h : (2 : ℝ) ^ (2 * (m : ℝ) + 1) ≤ (2 : ℝ) ^ (2 * x) := by
        rw [h22x]
        have e : (2 : ℝ) ^ (2 * (m : ℝ) + 1) = (2 : ℝ) ^ (2 * m + 1) := by
          rw [← Real.rpow_natCast]
          push_cast
          rfl
        rw [e]
        exact_mod_cast hge
      exact (Real.rpow_le_rpow_left_iff one_lt).1 h
    have hf : ⌊x + 1 / 2⌋ = (m : ℤ) + 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    rw [hf]
    push_cast
    ring

end OMA.P004257

theorem OMA.solution : type_of% @OMA.S_oeis_a004257.main := by
  intro n hn
  exact OMA.P004257.key n hn
