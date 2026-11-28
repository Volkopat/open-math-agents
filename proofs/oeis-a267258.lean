import OMAStatements.S_oeis_a267258

/-!
# A267258: the middle column of Rule 111

Rule 111 turns a cell OFF exactly when its left neighbour is ON and the cell agrees with its right
neighbour. From stage 5 on the pattern is a glider moving right one cell per stage: at odd stages
`t` exactly the cells `t - 4, t - 3, t - 2, t` are OFF, at even stages exactly the cells `t - 6`
and `t - 4, ..., t` are ON. So from stage 7 on the middle cell is ON exactly at odd stages.
-/

namespace OMA.S_oeis_a267258

open PowerSeries

lemma bit_iff (l c r : Bool) : Nat.testBit 111 (4 * l.toNat + 2 * c.toNat + r.toNat) = true ↔
    ¬(l = true ∧ (c = true ↔ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ x : ℤ, state 111 (t + 5) x = true ↔
    t % 2 = 0 ∧ ¬(t + 1 ≤ x ∧ x ≤ t + 3 ∨ x = t + 5) ∨
    t % 2 = 1 ∧ (x = t - 1 ∨ t + 1 ≤ x ∧ x ≤ t + 5) := by
  have r1 : ∀ x : ℤ, state 111 1 x = true ↔ x ≠ 1 := fun x => by
    simp only [state, step, bit_iff, decide_eq_true_eq]; omega
  have r2 : ∀ x : ℤ, state 111 2 x = true ↔ 0 ≤ x ∧ x ≤ 2 := fun x => by
    rw [state, step, bit_iff]; simp only [r1]; omega
  have r3 : ∀ x : ℤ, state 111 3 x = true ↔ x ≠ 1 ∧ x ≠ 3 := fun x => by
    rw [state, step, bit_iff]; simp only [r2]; omega
  have r4 : ∀ x : ℤ, state 111 4 x = true ↔ 0 ≤ x ∧ x ≤ 4 := fun x => by
    rw [state, step, bit_iff]; simp only [r3]; omega
  induction t with
  | zero => intro x; show state 111 5 x = true ↔ _; rw [state, step, bit_iff, r4, r4, r4]; omega
  | succ t ih => intro x; rw [state, step, bit_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : (2 * a (n + 7) : ℚ) = 4 * a (n + 6) + 1 + (-1) ^ n := by
  have h : a (n + 7) = 2 * a (n + 6) + c (n + 7) := by
    unfold a
    rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp hk), pow_succ]; ring
  rw [h, neg_one_pow_eq_pow_mod_two]
  unfold c
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · rw [(state_iff (n + 2) 0).2 (by omega), e]; simp; ring
  · rw [show state 111 (n + 7) 0 = false from
      Bool.eq_false_iff.2 fun h => by have := (state_iff (n + 2) 0).1 h; omega, e]; simp; ring

end OMA.S_oeis_a267258

open OMA.S_oeis_a267258 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267258.main := by
  have a6 : a 6 = 127 := by decide
  have K : ∀ n, 192 * (a (n + 6) : ℚ) = 24512 * 2 ^ n - 32 * (-1) ^ n - 96 := fun n => by
    induction n with
    | zero => norm_num [a6]
    | succ n ih => rw [pow_succ, pow_succ]; linarith [a_step n]
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [eq_div_iff (by norm_num)]
    linear_combination K m
  · have e : ∀ B : ℚ⟦X⟧, B * ((1 - X) * (1 + X) * (1 - 2 * X)) =
        B - C 2 * (B * X ^ 1) - B * X ^ 2 + C 2 * (B * X ^ 3) := fun B => by
      simp only [map_ofNat]; ring
    have key : A * ((1 - X) * (1 + X) * (1 - 2 * X)) = 1 + X - X ^ 8 := by
      rw [e, A]
      ext n
      simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X,
        coeff_mk]
      rcases Nat.lt_or_ge n 9 with h | h
      · have a7 : (a 7 : ℚ) = 255 := by have := a_step 0; norm_num [a6] at this; linarith
        have a8 : (a 8 : ℚ) = 510 := by have := a_step 1; norm_num [a7] at this; linarith
        interval_cases n <;> norm_num [a6, a7, a8, show a 0 = 1 by decide, show a 1 = 3 by decide,
          show a 2 = 7 by decide, show a 3 = 15 by decide, show a 4 = 31 by decide,
          show a 5 = 63 by decide]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
        have h1 : (2 * a (m + 9) : ℚ) = 4 * a (m + 8) + 1 + (-1) ^ (m + 2) := a_step (m + 2)
        rw [pow_succ, pow_succ] at h1
        have h2 := a_step m
        simp only [show 1 ≤ m + 9 by omega, show 2 ≤ m + 9 by omega, show 3 ≤ m + 9 by omega,
          show m + 9 ≠ 0 by omega, show m + 9 ≠ 1 by omega, show m + 9 ≠ 8 by omega, ↓reduceIte,
          show m + 9 - 1 = m + 8 from rfl, show m + 9 - 2 = m + 7 from rfl,
          show m + 9 - 3 = m + 6 from rfl]
        linarith
    rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one]
