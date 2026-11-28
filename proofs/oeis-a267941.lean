import OMAStatements.S_oeis_a267941
import Mathlib

/-!
Rule 253 switches a cell off only on the neighbourhood (0, 0, 1). From a single ON cell, stage 1
is everything except cell -1, and from stage 2 on every cell is ON. So a(n) = 2^(2n+1) - 1 for
n >= 2, with a(0) = 1 and a(1) = 3, which gives the recurrence and the generating function.
-/

namespace R253
open OMA.S_oeis_a267941 PowerSeries

theorem rule_eq (l c r : Bool) :
    Nat.testBit 253 (4 * l.toNat + 2 * c.toNat + r.toNat) = (l || c || !r) := by
  cases l <;> cases c <;> cases r <;> decide

theorem state_one (x : ℤ) : state 253 1 x = decide (x ≠ -1) := by
  show step 253 (state 253 0) x = _
  simp only [step, rule_eq, state]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem state_two (x : ℤ) : state 253 2 x = true := by
  show step 253 (state 253 1) x = _
  simp only [step, rule_eq, state_one]
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem state_all (n : ℕ) (x : ℤ) : state 253 (n + 2) x = true := by
  induction n generalizing x with
  | zero => exact state_two x
  | succ n ih =>
    show step 253 (state 253 (n + 2)) x = _
    simp only [step, ih, rule_eq, Bool.true_or]

theorem geom2 (m : ℕ) : ∑ i ∈ Finset.range m, (2 : ℤ) ^ i + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, pow_succ]; linarith

theorem a_eq (n : ℕ) (hn : 2 ≤ n) : (a n : ℤ) + 1 = 2 ^ (2 * n + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h : state 253 (k + 2) = fun _ => true := funext (state_all k)
  unfold a rowValue
  rw [h]
  push_cast
  simpa using geom2 (2 * (k + 2) + 1)

theorem a0 : a 0 = 1 := by decide

theorem a1 : a 1 = 3 := by decide

theorem recur (n : ℕ) (hn : 3 < n) : (a n : ℤ) = 5 * a (n - 1) - 4 * a (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
  have h4 := a_eq (m + 4) (by omega)
  have h3 := a_eq (m + 3) (by omega)
  have h2 := a_eq (m + 2) (by omega)
  linear_combination h4 - 5 * h3 + 4 * h2

end R253

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267941.main := by
  open OMA.S_oeis_a267941 R253 in
  refine ⟨recur, ?_⟩
  have e2 : (a 2 : ℤ) = 31 := by have := a_eq 2 (by omega); norm_num at this; linarith
  have e3 : (a 3 : ℤ) = 127 := by have := a_eq 3 (by omega); norm_num at this; linarith
  have q2 : (a 2 : ℚ) = 31 := by exact_mod_cast e2
  have q3 : (a 3 : ℚ) = 127 := by exact_mod_cast e3
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  rw [show ((1 - X) * (1 - 4 * X) : ℚ⟦X⟧) = 1 - C 5 * X ^ 1 + C 4 * X ^ 2 by
        simp only [map_ofNat]; ring,
      show (1 - 2 * X + 20 * X ^ 2 - 16 * X ^ 3 : ℚ⟦X⟧)
        = 1 - C 2 * X ^ 1 + C 20 * X ^ 2 - C 16 * X ^ 3 by simp only [map_ofNat]; ring,
      show ∀ p : ℚ⟦X⟧, p * (1 - C 5 * X ^ 1 + C 4 * X ^ 2)
        = p - C 5 * (p * X ^ 1) + C 4 * (p * X ^ 2) from fun p => by ring]
  ext n
  simp only [A, map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_one, coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp [a0]
  · simp [a0, a1]; norm_num
  · simp [a0, a1, q2]; norm_num
  · simp [a1, q2, q3]; norm_num
  · have h := recur (n + 4) (by omega)
    simp only [show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega] at h
    have hq : (a (n + 4) : ℚ) = 5 * a (n + 3) - 4 * a (n + 2) := by exact_mod_cast h
    simp only [show n + 1 + 1 + 1 + 1 = n + 4 by ring]
    simp [hq]
