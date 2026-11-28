import OMAStatements.S_oeis_a267538

/-!
# A267538: the middle column of Rule 143, written in base 10

Rule 143 turns a cell ON unless its left neighbour is ON while the cell or its right neighbour is
OFF. From row 2 on, exactly two cells are OFF, at `2 - t` and `3 - t`, so the middle cell is ON
from row 4 on and `a (n + 4) = 10 * a (n + 3) + 1`.
-/

namespace OMA.S_oeis_a267538

open PowerSeries

lemma rule_iff (l c r : Bool) : rule l c r = true ↔ (l = true → c = true ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ i : ℤ, state (t + 2) i = true ↔ i ≠ -t ∧ i ≠ 1 - t := by
  induction t with
  | zero => intro i; simp only [state, rule_iff, decide_eq_true_eq]; omega
  | succ t ih => intro i; rw [state, rule_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : a (n + 4) = 10 * a (n + 3) + 1 := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum, if_pos ((state_iff (n + 2) 0).2 (by omega)),
    Nat.sub_self]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp ht), pow_succ']
  split_ifs <;> rfl

end OMA.S_oeis_a267538

open OMA.S_oeis_a267538 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267538.main := by
  have H : ∀ n, 9 * a (n + 3) + 1 = 9901 * 10 ^ n := fun n => by
    induction n with
    | zero => decide
    | succ n ih => rw [a_step, pow_succ]; omega
  have R : ∀ n, (a (n + 5) : ℤ) = 11 * a (n + 4) - 10 * a (n + 3) := fun n => by
    have h1 : a (n + 5) = 10 * a (n + 4) + 1 := a_step (n + 1)
    have h2 := a_step n
    omega
  have Q : ∀ n, (a (n + 5) : ℚ) = 11 * a (n + 4) - 10 * a (n + 3) := fun n => by
    exact_mod_cast R n
  refine ⟨fun n hn => ?_, ?_, fun n => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    exact R m
  · have e : ∀ B : ℚ⟦X⟧, B * ((1 - X) * (1 - 10 * X)) =
        B - C 11 * (B * X ^ 1) + C 10 * (B * X ^ 2) := fun B => by simp only [map_ofNat]; ring
    have key : mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 10 * X)) = 1 - X ^ 2 + X ^ 4 := by
      rw [e]
      ext n
      simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_mk]
      rcases n with _ | _ | _ | _ | _ | n
      · norm_num [show a 0 = 1 by decide]
      · norm_num [show a 0 = 1 by decide, show a 1 = 11 by decide]
      · norm_num [show a 0 = 1 by decide, show a 1 = 11 by decide, show a 2 = 110 by decide]
      · norm_num [show a 1 = 11 by decide, show a 2 = 110 by decide, show a 3 = 1100 by decide]
      · norm_num [show a 2 = 110 by decide, show a 3 = 1100 by decide, show a 4 = 11001 by decide]
      · simp [Q n]
    rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one]
  · rcases n with _ | _ | _ | n
    · decide
    · decide
    · decide
    · have := H n
      show a (n + 3) = 9901 * 10 ^ (n + 3) / 9000
      rw [pow_succ, pow_succ, pow_succ]
      omega
