import OMAStatements.S_oeis_a267524

/-!
# A267524: the middle column of Rule 139

Under Rule 139 an ON cell stays ON when its right neighbour is ON, and an OFF cell turns ON when
its left neighbour is OFF. From stage 1 on, exactly two cells are OFF, at `1 - t` and `2 - t`, so
the middle cell is ON from stage 3 on and `a (n + 3) = 10 * a (n + 2) + 1`.
-/

namespace OMA.S_oeis_a267524

open PowerSeries

lemma bit_iff (l c r : Bool) : Nat.testBit 139 (4 * l.toNat + 2 * c.toNat + r.toNat) = true ↔
    (c = true → r = true) ∧ (l = true → c = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ x : ℤ, state 139 (t + 1) x = true ↔ x ≠ -t ∧ x ≠ 1 - t := by
  induction t with
  | zero => intro x; simp only [state, step, bit_iff, decide_eq_true_eq]; omega
  | succ t ih => intro x; rw [state, step, bit_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : a (n + 3) = 10 * a (n + 2) + 1 := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum, show c (n + 3) = 1 by
    unfold c; rw [(state_iff (n + 2) 0).2 (by omega)]; rfl, Nat.sub_self]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp hk), pow_succ]
  ring

end OMA.S_oeis_a267524

open OMA.S_oeis_a267524 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267524.main := by
  have R : ∀ n, (a (n + 4) : ℤ) = 11 * a (n + 3) - 10 * a (n + 2) := fun n => by
    have h1 : a (n + 4) = 10 * a (n + 3) + 1 := a_step (n + 1)
    have h2 := a_step n
    omega
  have Q : ∀ n, (a (n + 4) : ℚ) = 11 * a (n + 3) - 10 * a (n + 2) := fun n => by
    exact_mod_cast R n
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    exact R m
  · have e : ∀ B : ℚ⟦X⟧, B * ((1 - X) * (1 - 10 * X)) =
        B - C 11 * (B * X ^ 1) + C 10 * (B * X ^ 2) := fun B => by simp only [map_ofNat]; ring
    have key : A * ((1 - X) * (1 - 10 * X)) = 1 - X + X ^ 3 := by
      rw [e, A]
      ext n
      simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X,
        coeff_mk]
      rcases n with _ | _ | _ | _ | n
      · simp [show a 0 = 1 by decide]
      · norm_num [show a 0 = 1 by decide, show a 1 = 10 by decide]
      · norm_num [show a 0 = 1 by decide, show a 1 = 10 by decide, show a 2 = 100 by decide]
      · norm_num [show a 1 = 10 by decide, show a 2 = 100 by decide, show a 3 = 1001 by decide]
      · simp [Q n]
    rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one]
