import OMAStatements.S_oeis_a267604

/-!
# A267604: the middle column of Rule 175

Rule 175 turns a cell ON unless its left neighbour is ON and its right neighbour is OFF. From row 1
on, exactly one cell is OFF, at `2 - t`, so the middle cell is OFF only in row 2 and
`a (n + 3) = 2 * a (n + 2) + 1`.
-/

namespace OMA.S_oeis_a267604

open PowerSeries

lemma rule_iff (l c r : Bool) : rule l c r = true ↔ (l = true → r = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma row_iff (t : ℕ) : ∀ i : ℤ, row (t + 1) i = true ↔ i ≠ 1 - t := by
  induction t with
  | zero => intro i; simp only [row, rule_iff, decide_eq_true_eq]; omega
  | succ t ih => intro i; rw [row, rule_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : a (n + 3) = 2 * a (n + 2) + 1 := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum, if_pos ((row_iff (n + 2) 0).2 (by omega)),
    Nat.sub_self]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp ht), pow_succ']
  split_ifs <;> rfl

end OMA.S_oeis_a267604

open OMA.S_oeis_a267604 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267604.main := by
  have H : ∀ n, a (n + 2) + 1 = 7 * 2 ^ n := fun n => by
    induction n with
    | zero => decide
    | succ n ih => rw [a_step, pow_succ]; omega
  have R : ∀ n, (a (n + 4) : ℤ) = 3 * a (n + 3) - 2 * a (n + 2) := fun n => by
    have h1 : a (n + 4) = 2 * a (n + 3) + 1 := a_step (n + 1)
    have h2 := a_step n
    omega
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_, fun n => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    exact R m
  · have e : ∀ A : ℤ⟦X⟧, A * ((1 - X) * (1 - 2 * X)) = A - C 3 * (A * X ^ 1) + C 2 * (A * X ^ 2) :=
      fun A => by simp only [map_ofNat]; ring
    rw [e]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_mk]
    rcases n with _ | _ | _ | _ | n
    · simp [show a 0 = 1 by decide]
    · simp [show a 0 = 1 by decide, show a 1 = 3 by decide]
    · simp [show a 0 = 1 by decide, show a 1 = 3 by decide, show a 2 = 6 by decide]
    · simp [show a 1 = 3 by decide, show a 2 = 6 by decide, show a 3 = 13 by decide]
    · simp [R n]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have := H m
    simp only [A086224, Nat.add_sub_cancel]
    omega
  · rcases n with _ | _ | n
    · rw [show a 0 = 1 by decide, eq_comm, Int.ceil_eq_iff]; norm_num
    · rw [show a 1 = 3 by decide, eq_comm, Int.ceil_eq_iff]; norm_num
    · have h : (a (n + 2) : ℚ) + 1 = 7 * 2 ^ n := by exact_mod_cast H n
      rw [show (7 / 4 : ℚ) * 2 ^ (n + 2) - 1 = ((a (n + 2) : ℤ) : ℚ) by
        push_cast; rw [pow_add]; linarith, Int.ceil_intCast]
