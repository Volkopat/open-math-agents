import OMAStatements.S_oeis_a267708
import Mathlib

open OMA.S_oeis_a267708

theorem OMA.solution : type_of% @OMA.S_oeis_a267708.main := by
  have hs : ∀ t : ℕ, ∀ x : ℤ, state t x = decide (-(t : ℤ) ≤ x ∧ x ≤ 0) := by
    intro t
    induction t with
    | zero =>
      intro x
      simp only [state, Nat.cast_zero, neg_zero]
      by_cases h : x = 0
      · simp [h]
      · rw [decide_eq_false h, decide_eq_false (by omega)]
    | succ t ih =>
      intro x
      simp only [state, ih]
      push_cast
      rcases (by omega : x ≤ -(t : ℤ) - 2 ∨ x = -(t : ℤ) - 1 ∨ (-(t : ℤ) ≤ x ∧ x ≤ -1) ∨ x = 0 ∨
          1 ≤ x) with h | h | h | h | h
      · rw [decide_eq_false (by omega : ¬ (-(t : ℤ) ≤ x - 1 ∧ x - 1 ≤ 0)),
          decide_eq_false (by omega : ¬ (-(t : ℤ) ≤ x ∧ x ≤ 0)),
          decide_eq_false (by omega : ¬ (-(t : ℤ) ≤ x + 1 ∧ x + 1 ≤ 0)),
          decide_eq_false (by omega : ¬ (-((t : ℤ) + 1) ≤ x ∧ x ≤ 0))]
        rfl
      · rw [decide_eq_false (by omega : ¬ (-(t : ℤ) ≤ x - 1 ∧ x - 1 ≤ 0)),
          decide_eq_false (by omega : ¬ (-(t : ℤ) ≤ x ∧ x ≤ 0)),
          decide_eq_true (by omega : (-(t : ℤ) ≤ x + 1 ∧ x + 1 ≤ 0)),
          decide_eq_true (by omega : (-((t : ℤ) + 1) ≤ x ∧ x ≤ 0))]
        rfl
      · rw [decide_eq_true (by omega : (-(t : ℤ) ≤ x ∧ x ≤ 0)),
          decide_eq_true (by omega : (-(t : ℤ) ≤ x + 1 ∧ x + 1 ≤ 0)),
          decide_eq_true (by omega : (-((t : ℤ) + 1) ≤ x ∧ x ≤ 0))]
        cases decide (-(t : ℤ) ≤ x - 1 ∧ x - 1 ≤ 0) <;> rfl
      · rw [decide_eq_true (by omega : (-(t : ℤ) ≤ x ∧ x ≤ 0)),
          decide_eq_false (by omega : ¬ (-(t : ℤ) ≤ x + 1 ∧ x + 1 ≤ 0)),
          decide_eq_true (by omega : (-((t : ℤ) + 1) ≤ x ∧ x ≤ 0))]
        cases decide (-(t : ℤ) ≤ x - 1 ∧ x - 1 ≤ 0) <;> rfl
      · rw [decide_eq_false (by omega : ¬ (-(t : ℤ) ≤ x ∧ x ≤ 0)),
          decide_eq_false (by omega : ¬ (-(t : ℤ) ≤ x + 1 ∧ x + 1 ≤ 0)),
          decide_eq_false (by omega : ¬ (-((t : ℤ) + 1) ≤ x ∧ x ≤ 0))]
        cases decide (-(t : ℤ) ≤ x - 1 ∧ x - 1 ≤ 0) <;> rfl
  intro n
  have h1 := Nat.sqrt_le' n
  have h2 := Nat.lt_succ_sqrt' n
  set t := Nat.sqrt n with ht
  simp only [term, ← ht, hs]
  rw [Nat.succ_eq_add_one] at h2
  by_cases hc : n ≤ t * t + t
  · have e : Nat.sqrt (4 * n) = 2 * t := by
      symm; rw [Nat.eq_sqrt]; constructor <;> nlinarith
    rw [e, decide_eq_true (by push_cast; constructor <;> nlinarith)]
    rw [pow_mul]; norm_num
  · have e : Nat.sqrt (4 * n) = 2 * t + 1 := by
      symm; rw [Nat.eq_sqrt]; constructor <;> nlinarith
    rw [e, decide_eq_false (by push_cast; intro h; have := h.2; have hc2 := not_le.mp hc; nlinarith)]
    rw [pow_succ, pow_mul]; norm_num
