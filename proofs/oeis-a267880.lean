import OMAStatements.S_oeis_a267880

/-!
# A267880: the middle column of Rule 233

Rule 233 turns a cell ON when at least two of the three cells above it are ON, or when all three
are OFF. Every cell is ON from stage 4 on, so `a (n + 4) = 2 * a (n + 3) + 1`.
-/

namespace OMA.S_oeis_a267880

open PowerSeries

lemma eca_iff (l c r : Bool) : eca 233 l c r = true ↔ (l = true ∧ c = true) ∨
    (l = true ∧ r = true) ∨ (c = true ∧ r = true) ∨ ¬(l = true ∨ c = true ∨ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_on (t : ℕ) : ∀ i : ℤ, state (t + 4) i = true := by
  have r1 : ∀ i : ℤ, state 1 i = true ↔ i < -1 ∨ 1 < i := fun i => by
    simp only [state, eca_iff, decide_eq_true_eq]; omega
  have r2 : ∀ i : ℤ, state 2 i = true ↔ i ≠ -1 ∧ i ≠ 1 := fun i => by
    rw [state, eca_iff]; simp only [r1]; omega
  have r3 : ∀ i : ℤ, state 3 i = true ↔ i ≠ 0 := fun i => by
    rw [state, eca_iff]; simp only [r2]; omega
  induction t with
  | zero => intro i; rw [state, eca_iff]; simp only [r3]; omega
  | succ t ih => intro i; rw [state, ih, ih, ih]; rfl

lemma a_step (n : ℕ) : a (n + 4) = 2 * a (n + 3) + 1 := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum, if_pos (state_on n 0), Nat.sub_self]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp ht), pow_succ']
  split_ifs <;> rfl

end OMA.S_oeis_a267880

open OMA.S_oeis_a267880 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267880.main := by
  have R : ∀ n, (a (n + 5) : ℤ) = 3 * a (n + 4) - 2 * a (n + 3) := fun n => by
    have h1 : a (n + 5) = 2 * a (n + 4) + 1 := a_step (n + 1)
    have h2 := a_step n
    omega
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    exact R m
  · have e : ∀ B : ℤ⟦X⟧, B * ((1 - X) * (1 - 2 * X)) = B - C 3 * (B * X ^ 1) + C 2 * (B * X ^ 2) :=
      fun B => by simp only [map_ofNat]; ring
    rw [e]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X,
      coeff_mk]
    rcases n with _ | _ | _ | _ | _ | n
    · norm_num [show a 0 = 1 by decide]
    · norm_num [show a 0 = 1 by decide, show a 1 = 2 by decide]
    · norm_num [show a 0 = 1 by decide, show a 1 = 2 by decide, show a 2 = 5 by decide]
    · norm_num [show a 1 = 2 by decide, show a 2 = 5 by decide, show a 3 = 10 by decide]
    · norm_num [show a 2 = 5 by decide, show a 3 = 10 by decide, show a 4 = 21 by decide]
    · simp [R n]
