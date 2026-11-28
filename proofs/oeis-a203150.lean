import OMAStatements.S_oeis_a203150
import Mathlib

namespace OMA.P203150

open OMA.S_oeis_a203150

/-- The repeating sequence. -/
def x (i : ℕ) : ℤ := digit i

/-- The product of the first n terms. -/
def p (n : ℕ) : ℤ := (products n).1

/-- The sum of the products omitting one factor. -/
def b (n : ℕ) : ℤ := (products n).2

lemma a_eq_b (n : ℕ) : a n = b n := rfl

lemma b_zero : b 0 = 0 := rfl

lemma p_zero : p 0 = 1 := rfl

lemma b_succ (n : ℕ) : b (n + 1) = p n + x n * b n := by
  unfold b p x
  rcases h : products n with ⟨u, v⟩
  simp [products, h]
  ring

lemma p_succ (n : ℕ) : p (n + 1) = x n * p n := by
  unfold p x
  rcases h : products n with ⟨u, v⟩
  simp [products, h]
  ring

lemma x_even (k : ℕ) : x (2 * k) = 1 := by
  unfold x digit
  simp

lemma x_odd (k : ℕ) : x (2 * k + 1) = 2 := by
  unfold x digit
  have h : (2 * k + 1) % 2 = 1 := by omega
  simp [h]

lemma closed (k : ℕ) : p (2 * k) = 2 ^ k ∧ 2 * b (2 * k) = 3 * (k : ℤ) * 2 ^ k := by
  induction k with
  | zero => simp [p_zero, b_zero]
  | succ k ih =>
    obtain ⟨hp, hb⟩ := ih
    have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    have hp1 : p (2 * k + 1) = 2 ^ k := by
      rw [p_succ, x_even, hp]
      ring
    have hb1 : b (2 * k + 1) = 2 ^ k + b (2 * k) := by
      rw [b_succ, x_even, hp]
      ring
    constructor
    · rw [e, p_succ, x_odd, hp1]
      ring
    · rw [e, b_succ, x_odd, hp1, hb1]
      push_cast
      linear_combination 2 * hb

lemma final (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) = (6 * Real.sqrt 2 * (n : ℝ)
        + (1 + 3 * (1 - Real.sqrt 2) * (n : ℝ)) * (1 - (-1 : ℝ) ^ n))
      * Real.sqrt 2 ^ (n - 1) / 8 := by
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq]
    exact hr
  have hpow : ∀ k : ℕ, Real.sqrt 2 ^ (2 * k) = 2 ^ k := by
    intro k
    rw [pow_mul, hr]
  rw [a_eq_b n]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hb := (closed (j + 1)).2
    have hbR : (2 : ℝ) * ((b (2 * (j + 1)) : ℤ) : ℝ) = 3 * ((j : ℝ) + 1) * 2 ^ (j + 1) := by
      exact_mod_cast hb
    have e1 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    have e2 : (-1 : ℝ) ^ (2 * (j + 1)) = 1 := by
      rw [pow_mul]
      norm_num
    have e3 : Real.sqrt 2 ^ (2 * (j + 1) - 1) = 2 ^ j * Real.sqrt 2 := by
      rw [e1, pow_succ, hpow]
    rw [e3, e2]
    push_cast
    linear_combination (1 / 2 : ℝ) * hbR - (3 / 2 * ((j : ℝ) + 1) * 2 ^ j) * h2
  · have hp := (closed k).1
    have hb := (closed k).2
    have hb1 : b (2 * k + 1) = 2 ^ k + b (2 * k) := by
      rw [b_succ, x_even, hp]
      ring
    have hbR : (2 : ℝ) * ((b (2 * k) : ℤ) : ℝ) = 3 * (k : ℝ) * 2 ^ k := by
      exact_mod_cast hb
    have hb1R : ((b (2 * k + 1) : ℤ) : ℝ) = 2 ^ k + ((b (2 * k) : ℤ) : ℝ) := by
      exact_mod_cast hb1
    have e2 : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    have e3 : Real.sqrt 2 ^ (2 * k + 1 - 1) = 2 ^ k := by
      rw [Nat.add_sub_cancel, hpow]
    rw [e3, e2]
    push_cast
    linear_combination hb1R + (1 / 2 : ℝ) * hbR

end OMA.P203150

theorem OMA.solution : type_of% @OMA.S_oeis_a203150.main := by
  intro n hn
  exact OMA.P203150.final n hn
