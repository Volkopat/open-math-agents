import OMAStatements.S_oeis_a267539

/-!
# A267539: the middle column of Rule 143

Rule 143 turns a cell ON unless its left neighbour is ON while the cell or its right neighbour is
OFF. From row 2 on, exactly two cells are OFF, at `2 - t` and `3 - t`, so the middle cell is ON
from row 4 on and `a (n + 4) = 2 * a (n + 3) + 1`.
-/

namespace OMA.S_oeis_a267539

open PowerSeries

lemma rule_iff (l c r : Bool) : rule l c r = true ↔ (l = true → c = true ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma row_iff (t : ℕ) : ∀ i : ℤ, row (t + 2) i = true ↔ i ≠ -t ∧ i ≠ 1 - t := by
  induction t with
  | zero => intro i; simp only [row, rule_iff, decide_eq_true_eq]; omega
  | succ t ih => intro i; rw [row, rule_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : a (n + 4) = 2 * a (n + 3) + 1 := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum, if_pos ((row_iff (n + 2) 0).2 (by omega)),
    Nat.sub_self]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp ht), pow_succ']
  split_ifs <;> rfl

end OMA.S_oeis_a267539

open OMA.S_oeis_a267539 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267539.main := by
  have H : ∀ n, a (n + 3) + 1 = 13 * 2 ^ n := fun n => by
    induction n with
    | zero => decide
    | succ n ih => rw [a_step, pow_succ]; omega
  have R : ∀ n, (a (n + 5) : ℤ) = 3 * a (n + 4) - 2 * a (n + 3) := fun n => by
    have h1 : a (n + 5) = 2 * a (n + 4) + 1 := a_step (n + 1)
    have h2 := a_step n
    omega
  refine ⟨fun n hn => ?_, ?_, by decide, by decide, by decide, fun n => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    exact R m
  · have e : ∀ A : ℤ⟦X⟧, A * ((1 - X) * (1 - 2 * X)) = A - C 3 * (A * X ^ 1) + C 2 * (A * X ^ 2) :=
      fun A => by simp only [map_ofNat]; ring
    rw [e]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_mk]
    rcases n with _ | _ | _ | _ | _ | n
    · simp [show a 0 = 1 by decide]
    · simp [show a 0 = 1 by decide, show a 1 = 3 by decide]
    · simp [show a 0 = 1 by decide, show a 1 = 3 by decide, show a 2 = 6 by decide]
    · simp [show a 1 = 3 by decide, show a 2 = 6 by decide, show a 3 = 12 by decide]
    · simp [show a 2 = 6 by decide, show a 3 = 12 by decide, show a 4 = 25 by decide]
    · simp [R n]
  · have := H n
    unfold A198274
    omega
