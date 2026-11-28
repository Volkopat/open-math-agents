import OMAStatements.S_oeis_a284005
import Mathlib
open OMA.S_oeis_a284005
lemma weight_even (x : ℕ) : weight (2 * x) = weight x := by
  rcases x.eq_zero_or_pos with h | h
  · subst h; rfl
  · unfold weight
    rw [Nat.digits_def' (by norm_num) (by omega)]
    rw [show 2 * x % 2 = 0 by omega, show 2 * x / 2 = x by omega]
    simp

lemma weight_odd (x : ℕ) : weight (2 * x + 1) = weight x + 1 := by
  unfold weight
  rw [Nat.digits_def' (by norm_num) (by omega)]
  rw [show (2 * x + 1) % 2 = 1 by omega, show (2 * x + 1) / 2 = x by omega]
  simp [add_comm]

lemma a_even (x : ℕ) : a (2 * x) = (1 + weight x) * a x := by
  rcases x.eq_zero_or_pos with h | h
  · subst h; simp [a, weight]
  · rw [a, if_neg (by omega), weight_even, show 2 * x / 2 = x by omega]

lemma a_odd (x : ℕ) : a (2 * x + 1) = (2 + weight x) * a x := by
  rw [a, if_neg (by omega), weight_odd, show (2 * x + 1) / 2 = x by omega]
  ring

lemma weight_pow (k n : ℕ) : weight (2 ^ k * n) = weight n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_comm _ 2, mul_assoc, weight_even, ih]

lemma a_pow (k n : ℕ) : a (2 ^ k * n) = (1 + weight n) ^ k * a n := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_comm _ 2, mul_assoc, a_even, ih, weight_pow]; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a284005.main := by
  intro m n
  rw [a_pow, a_odd, weight_odd]
  simp_rw [a_pow]
  have h := add_pow (1 + weight n) 1 (m + 1)
  simp only [one_pow, mul_one] at h
  rw [show (1 + (weight n + 1)) ^ m * ((2 + weight n) * a n)
      = (1 + weight n + 1) ^ (m + 1) * a n by ring, h, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => by push_cast; ring
