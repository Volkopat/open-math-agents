import OMAStatements.S_oeis_a267774
import Mathlib

/-!
Rule 207 switches a cell off only when its left neighbour is ON and the cell itself is OFF.
From a single ON cell, every stage n >= 1 is ON everywhere except at cell 1. Cell 1 is digit
n - 1 of row n, so a(n) = 2^(2n+1) - 1 - 2^(n-1) for n >= 1, which gives the recurrence with
characteristic roots 1, 2, 4 and the generating function.
-/

namespace R207
open OMA.S_oeis_a267774 PowerSeries

theorem rule_eq (l c r : Bool) :
    Nat.testBit 207 (4 * l.toNat + 2 * c.toNat + r.toNat) = (!l || c) := by
  cases l <;> cases c <;> cases r <;> decide

theorem state_succ (n : ℕ) (x : ℤ) : state 207 (n + 1) x = decide (x ≠ 1) := by
  induction n generalizing x with
  | zero =>
    show step 207 (state 207 0) x = _
    simp only [step, rule_eq, state]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  | succ n ih =>
    show step 207 (state 207 (n + 1)) x = _
    simp only [step, rule_eq, ih]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    omega

theorem geom2 (m : ℕ) : ∑ i ∈ Finset.range m, 2 ^ i + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem a_eq (k : ℕ) : a (k + 1) + 1 + 2 ^ k = 2 ^ (2 * (k + 1) + 1) := by
  have h : state 207 (k + 1) = fun x => decide (x ≠ 1) := funext (state_succ k)
  have hk : k ∈ Finset.range (2 * (k + 1) + 1) := Finset.mem_range.mpr (by omega)
  have hsum : rowValue (fun x => decide (x ≠ 1)) (k + 1)
      = ∑ i ∈ Finset.range (2 * (k + 1) + 1), (if i = k then 0 else 2 ^ i) := by
    unfold rowValue
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = k
    · subst hi
      simp
    · rw [if_neg hi]
      have hd : decide (((k + 1 : ℕ) : ℤ) - (i : ℤ) ≠ 1) = true := by
        rw [decide_eq_true_eq]
        push_cast
        omega
      simp only [hd, Bool.toNat_true, one_mul]
  have hsplit : ∑ i ∈ Finset.range (2 * (k + 1) + 1), (if i = k then 0 else 2 ^ i) + 2 ^ k
      = ∑ i ∈ Finset.range (2 * (k + 1) + 1), 2 ^ i := by
    have e : ∑ i ∈ Finset.range (2 * (k + 1) + 1), (if i = k then 2 ^ i else 0) = 2 ^ k := by
      rw [Finset.sum_ite_eq', if_pos hk]
    rw [← e, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have g := geom2 (2 * (k + 1) + 1)
  unfold a
  rw [h, hsum]
  omega

theorem a_eqZ (n : ℕ) (hn : 1 ≤ n) : (a n : ℤ) + 1 + 2 ^ (n - 1) = 2 ^ (2 * n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact_mod_cast a_eq k

theorem a0 : a 0 = 1 := by decide

theorem recur (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  have h4 := a_eqZ (m + 4) (by omega)
  have h3 := a_eqZ (m + 3) (by omega)
  have h2 := a_eqZ (m + 2) (by omega)
  have h1 := a_eqZ (m + 1) (by omega)
  rw [show m + 4 - 1 = m + 3 by omega] at h4
  rw [show m + 3 - 1 = m + 2 by omega] at h3
  rw [show m + 2 - 1 = m + 1 by omega] at h2
  rw [show m + 1 - 1 = m by omega] at h1
  linear_combination h4 - 7 * h3 + 14 * h2 - 8 * h1

end R207

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267774.main := by
  open OMA.S_oeis_a267774 R207 in
  refine ⟨recur, ?_⟩
  have e1 : a 1 = 6 := by have := a_eq 0; norm_num at this; omega
  have e2 : a 2 = 29 := by have := a_eq 1; norm_num at this; omega
  have e3 : a 3 = 123 := by have := a_eq 2; norm_num at this; omega
  have q1 : (a 1 : ℚ) = 6 := by exact_mod_cast e1
  have q2 : (a 2 : ℚ) = 29 := by exact_mod_cast e2
  have q3 : (a 3 : ℚ) = 123 := by exact_mod_cast e3
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  rw [show ((1 - X) * (1 - 2 * X) * (1 - 4 * X) : ℚ⟦X⟧)
        = 1 - C 7 * X ^ 1 + C 14 * X ^ 2 - C 8 * X ^ 3 by simp only [map_ofNat]; ring,
      show (1 - X + X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) = 1 - X ^ 1 + X ^ 2 - C 4 * X ^ 3 by
        simp only [map_ofNat]; ring,
      show ∀ p : ℚ⟦X⟧, p * (1 - C 7 * X ^ 1 + C 14 * X ^ 2 - C 8 * X ^ 3)
        = p - C 7 * (p * X ^ 1) + C 14 * (p * X ^ 2) - C 8 * (p * X ^ 3) from fun p => by ring]
  ext n
  simp only [A, map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp [a0]
  · simp [a0, q1]; norm_num
  · simp [a0, q1, q2, coeff_X] <;> norm_num
  · simp [a0, q1, q2, q3, coeff_X] <;> norm_num
  · have h := recur (n + 4) (by omega)
    simp only [show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega,
      show n + 4 - 3 = n + 1 by omega] at h
    have hq : (a (n + 4) : ℚ) = 7 * a (n + 3) - 14 * a (n + 2) + 8 * a (n + 1) := by
      exact_mod_cast h
    simp only [show n + 1 + 1 + 1 + 1 = n + 4 by ring]
    simp [hq, coeff_X] <;> ring
