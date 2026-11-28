import OMAStatements.S_mo_408352
import Mathlib

open OMA.S_mo_408352
open Finset

namespace P408352

def pr (c : ℕ → ZMod 2) : ℕ → ZMod 2
  | 0 => 0
  | 1 => c 0
  | (j + 2) => pr c j + c (j + 1)

theorem pr_odd (c : ℕ → ZMod 2) (k : ℕ) :
    pr c (2 * k + 1) = ∑ m ∈ range (k + 1), c (2 * m) := by
  induction k with
  | zero => simp [pr]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, pr, ih, sum_range_succ _ (k + 1),
      show 2 * k + 1 + 1 = 2 * (k + 1) by ring]

theorem ev (bits : ℕ → ZMod 2) (K : ℕ) :
    evenParity (2 * K + 1) bits = ∑ m ∈ range (K + 1), bits (2 * m) := by
  induction K with
  | zero => simp [evenParity]
  | succ K ih =>
    unfold evenParity at ih ⊢
    rw [show 2 * (K + 1) + 1 = (2 * K + 1) + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ _ (K + 1)]
    have h2 : (2 * K + 1 + 1) % 2 = 0 := by omega
    rw [if_neg (by omega), if_pos h2, show 2 * K + 1 + 1 = 2 * (K + 1) by ring, add_zero]

theorem key (K : ℕ) (bits : ℕ → ZMod 2) (h : ∑ m ∈ range (K + 1), (1 + bits (2 * m)) = 0) :
    reachable (2 * K + 1) bits := by
  refine ⟨pr (fun t => 1 + bits t), fun i hi => ?_⟩
  rcases i with _ | j
  · rw [if_pos rfl]
    by_cases hK : 0 + 1 < 2 * K + 1
    · rw [if_pos hK]
      show bits 0 + 0 + (1 + bits 0) = 1
      generalize bits 0 = x
      revert x
      decide
    · rw [if_neg hK]
      have hK0 : K = 0 := by omega
      subst hK0
      rw [sum_range_one, mul_zero] at h
      revert h
      generalize bits 0 = x
      revert x
      decide
  · rw [if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel]
    by_cases hj : j + 1 + 1 < 2 * K + 1
    · rw [if_pos hj]
      show bits (j + 1) + pr _ j + (pr _ j + (1 + bits (j + 1))) = 1
      generalize bits (j + 1) = x
      generalize pr (fun t => 1 + bits t) j = y
      revert x y
      decide
    · rw [if_neg hj]
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      have hj' : j = 2 * k + 1 := by omega
      subst hj'
      rw [pr_odd, show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
      rw [sum_range_succ] at h
      revert h
      generalize bits (2 * (k + 1)) = x
      generalize ∑ m ∈ range (k + 1), (1 + bits (2 * m)) = y
      revert x y
      decide

end P408352

theorem OMA.solution : type_of% @OMA.S_mo_408352.main := by
  have two : (2 : ZMod 2) = 0 := rfl
  constructor
  · intro n bits h
    rw [show 4 * n + 1 = 2 * (2 * n) + 1 by ring] at h ⊢
    apply P408352.key
    rw [P408352.ev] at h
    rw [sum_add_distrib, h, sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast
    simp only [two, zero_mul, zero_add, add_zero]
    decide
  · intro n bits h
    rw [show 4 * n + 3 = 2 * (2 * n + 1) + 1 by ring] at h ⊢
    apply P408352.key
    rw [P408352.ev] at h
    rw [sum_add_distrib, h, sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast
    simp only [two, zero_mul, zero_add, add_zero]
    decide
