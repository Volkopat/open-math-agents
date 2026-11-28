import OMAStatements.S_oeis_a044140
import Mathlib

/-!
# A044140: the conjectured recurrence fails at `n = 58`

Counting the terms below a given bound shows `a 49 = 2109`, `a 50 = 2158`, `a 57 = 2452` and
`a 58 = 2499`.  The recurrence would give `a 58 = 2452 + 2158 - 2109 = 2501`.
-/

namespace OMA.S_oeis_a044140

instance : DecidablePred Has02 := fun m => by unfold Has02; infer_instance
instance : DecidablePred IsTerm := fun k => by unfold IsTerm; infer_instance

lemma c49 : Nat.count IsTerm 2109 = 48 ∧ IsTerm 2109 := by decide +kernel
lemma c50 : Nat.count IsTerm 2158 = 49 ∧ IsTerm 2158 := by decide +kernel
lemma c57 : Nat.count IsTerm 2452 = 56 ∧ IsTerm 2452 := by decide +kernel
lemma c58 : Nat.count IsTerm 2499 = 57 ∧ IsTerm 2499 := by decide +kernel

lemma a_eq {n k : ℕ} (h : Nat.count IsTerm k = n ∧ IsTerm k) : a (n + 1) = k := by
  unfold a
  rw [Nat.add_sub_cancel, ← h.1]
  exact Nat.nth_count h.2

end OMA.S_oeis_a044140

open OMA.S_oeis_a044140 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a044140.main) := by
  intro h
  have h58 := h 58 (by norm_num)
  have e1 : (58 : ℕ) - 1 = 56 + 1 := rfl
  have e2 : (58 : ℕ) - 8 = 49 + 1 := rfl
  have e3 : (58 : ℕ) - 9 = 48 + 1 := rfl
  have e0 : (58 : ℕ) = 57 + 1 := rfl
  rw [e1, e2, e3] at h58
  rw [e0, a_eq c58, a_eq c57, a_eq c50, a_eq c49] at h58
  norm_num at h58
