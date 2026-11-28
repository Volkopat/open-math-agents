import OMAStatements.S_oeis_a231897
import Mathlib

open OMA.S_oeis_a231897

namespace OMA.P_oeis_a231897

theorem wt_rec (x : ℕ) (hx : 0 < x) : wt x = x % 2 + wt (x / 2) := by
  unfold wt
  rw [Nat.digits_def' (by norm_num) hx]
  simp

theorem wt_double (x : ℕ) : wt (2 * x) = wt x := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [wt_rec (2 * x) (by omega)]
    have h1 : 2 * x % 2 = 0 := by omega
    have h2 : 2 * x / 2 = x := by omega
    rw [h1, h2, zero_add]

theorem wt_odd (x : ℕ) : wt (1 + 2 * x) = 1 + wt x := by
  rw [wt_rec (1 + 2 * x) (by omega)]
  have h1 : (1 + 2 * x) % 2 = 1 := by omega
  have h2 : (1 + 2 * x) / 2 = x := by omega
  rw [h1, h2]

theorem wt_pow_mul (k y : ℕ) : wt (2 ^ k * y) = wt y := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc, wt_double, ih]

theorem wt_mersenne (j : ℕ) : wt (2 ^ j - 1) = j := by
  induction j with
  | zero => simp [wt]
  | succ j ih =>
    have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have : 2 ^ (j + 1) - 1 = 1 + 2 * (2 ^ j - 1) := by rw [pow_succ]; omega
    rw [this, wt_odd, ih]; ring

end OMA.P_oeis_a231897

open OMA.P_oeis_a231897 in
theorem OMA.solution : type_of% @OMA.S_oeis_a231897.main := by
  intro n
  rcases n with _ | k
  · exact ⟨0, by simp [wt]⟩
  · refine ⟨2 ^ (k + 1) - 1, ?_⟩
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ k = s + 1 := ⟨2 ^ k - 1, by have := @Nat.one_le_two_pow k; omega⟩
    have hsk : s = 2 ^ k - 1 := by omega
    have e : (2 ^ (k + 1) - 1) ^ 2 = 1 + 2 * (2 ^ (k + 1) * s) := by
      have h2 : 2 ^ (k + 1) = (s + 1) * 2 := by rw [pow_succ, hs]
      rw [h2]
      have : (s + 1) * 2 - 1 = 2 * s + 1 := by omega
      rw [this]; ring
    rw [e, wt_odd, wt_pow_mul, hsk, wt_mersenne]; ring
