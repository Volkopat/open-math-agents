import OMAStatements.S_oeis_a267044

/-!
# A267044: the middle column of Rule 91, written in base 10

Rule 91 turns a cell ON when its two neighbours differ, or when all three cells are OFF. From
stage 3 on the pattern has period 2: at odd stages exactly the cells `-1, 0, 1` are OFF, at even
stages exactly the cells `-2, ..., 2` are ON. So the middle cell of stage `n + 3` is ON exactly
when `n` is odd.
-/

namespace OMA.S_oeis_a267044

open PowerSeries

lemma bit_iff (l c r : Bool) : Nat.testBit 91 (4 * l.toNat + 2 * c.toNat + r.toNat) = true ↔
    ¬(l = true ↔ r = true) ∨ ¬(l = true ∨ c = true ∨ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ x : ℤ, state 91 (t + 3) x = true ↔
    t % 2 = 0 ∧ (x < -1 ∨ 1 < x) ∨ t % 2 = 1 ∧ -2 ≤ x ∧ x ≤ 2 := by
  have r2 : ∀ x : ℤ, state 91 2 x = true ↔ x = -1 ∨ x = 1 := fun x => by
    simp only [state, step, bit_iff, decide_eq_true_eq]; omega
  induction t with
  | zero => intro x; show state 91 3 x = true ↔ _; rw [state, step, bit_iff, r2, r2, r2]; omega
  | succ t ih => intro x; rw [state, step, bit_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : (2 * a (n + 3) : ℚ) = 20 * a (n + 2) + 1 - (-1) ^ n := by
  have h : a (n + 3) = 10 * a (n + 2) + c (n + 3) := by
    unfold a
    rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp hk), pow_succ]; ring
  rw [h, neg_one_pow_eq_pow_mod_two]
  unfold c
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · rw [show state 91 (n + 3) 0 = false from
      Bool.eq_false_iff.2 fun h => by have := (state_iff n 0).1 h; omega, e]; simp; ring
  · rw [(state_iff n 0).2 (by omega), e]; simp; ring

end OMA.S_oeis_a267044

open OMA.S_oeis_a267044 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267044.main := by
  have K : ∀ n, 9900 * (a (n + 2) : ℚ) = -550 + 450 * (-1) ^ n + 990100 * 10 ^ n := fun n => by
    induction n with
    | zero => norm_num [show a 2 = 100 by decide]
    | succ n ih => rw [pow_succ, pow_succ]; linarith [a_step n]
  have P : ∀ n, 4 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3) := fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h1 : (2 * a (m + 5) : ℚ) = 20 * a (m + 4) + 1 - (-1) ^ (m + 2) := a_step (m + 2)
    rw [pow_succ, pow_succ] at h1
    have : (a (m + 5) : ℚ) = 10 * a (m + 4) + a (m + 3) - 10 * a (m + 2) := by
      linarith [a_step m]
    show (a (m + 5) : ℤ) = 10 * a (m + 4) + a (m + 3) - 10 * a (m + 2)
    exact_mod_cast this
  refine ⟨fun n hn => ?_, P, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [eq_div_iff (by norm_num)]
    linear_combination K m
  · have e : ∀ B : ℚ⟦X⟧, B * ((1 - X) * (1 + X) * (1 - 10 * X)) =
        B - C 10 * (B * X ^ 1) - B * X ^ 2 + C 10 * (B * X ^ 3) := fun B => by
      simp only [map_ofNat]; ring
    have key : A * ((1 - X) * (1 + X) * (1 - 10 * X)) = 1 - X ^ 2 + X ^ 4 := by
      rw [e, A]
      ext n
      simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_mk]
      rcases Nat.lt_or_ge n 5 with h | h
      · interval_cases n <;> norm_num [show a 0 = 1 by decide, show a 1 = 10 by decide,
          show a 2 = 100 by decide, show a 3 = 1000 by decide, show a 4 = 10001 by decide]
      · have q : (a n : ℚ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3) := by
          exact_mod_cast P n h
        split_ifs <;> first | omega | linarith
    rw [← key, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one]
