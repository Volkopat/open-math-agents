import OMAStatements.S_oeis_a266592

/-!
# A266592: the middle column of Rule 37, written in base 10

Rule 37 turns a cell ON when its two neighbours agree and are not both ON together with the cell.
From stage 2 on the pattern has period 2: at even stages exactly the cells `-1, 0, 1` are ON, at
odd stages exactly the cells `-2, ..., 2` are OFF. So the middle cell of stage `n + 2` is ON
exactly when `n` is even.
-/

namespace OMA.S_oeis_a266592

open PowerSeries

lemma eca_iff (l c r : Bool) : eca 37 l c r = true ↔
    (l = true ↔ r = true) ∧ ¬(l = true ∧ c = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ i : ℤ, state (t + 2) i = true ↔
    t % 2 = 0 ∧ -1 ≤ i ∧ i ≤ 1 ∨ t % 2 = 1 ∧ (i < -2 ∨ 2 < i) := by
  have r1 : ∀ i : ℤ, state 1 i = true ↔ i ≠ -1 ∧ i ≠ 1 := fun i => by
    simp only [state, eca_iff, decide_eq_true_eq]; omega
  induction t with
  | zero => intro i; show state 2 i = true ↔ _; rw [state, eca_iff, r1, r1, r1]; omega
  | succ t ih => intro i; rw [state, eca_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : (2 * a (n + 2) : ℤ) = 20 * a (n + 1) + 1 + (-1) ^ n := by
  have h : a (n + 2) = 10 * a (n + 1) + if state (n + 2) 0 then 1 else 0 := by
    unfold a
    rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp ht), pow_succ']
    split_ifs <;> rfl
  rw [h, neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · rw [if_pos ((state_iff n 0).2 (by omega)), e]; push_cast; ring
  · rw [if_neg fun h => by have := (state_iff n 0).1 h; omega, e]; push_cast; ring

end OMA.S_oeis_a266592

open OMA.S_oeis_a266592 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a266592.main := by
  have K : ∀ n, 990 * (a (n + 1) : ℤ) = -45 * (-1) ^ n + 10990 * 10 ^ n - 55 := fun n => by
    induction n with
    | zero => norm_num [show a 1 = 11 by decide]
    | succ n ih => rw [pow_succ, pow_succ]; linarith [a_step n]
  have P : ∀ n, 3 < n → (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3) := fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h1 : (2 * a (m + 4) : ℤ) = 20 * a (m + 3) + 1 + (-1) ^ (m + 2) := a_step (m + 2)
    rw [pow_succ, pow_succ] at h1
    show (a (m + 4) : ℤ) = 10 * a (m + 3) + a (m + 2) - 10 * a (m + 1)
    linarith [a_step m]
  refine ⟨fun n hn => ?_, P, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [K m]; ring
  · have e : ∀ B : ℤ⟦X⟧, B * ((1 - X) * (1 + X) * (1 - 10 * X)) =
        B - C 10 * (B * X ^ 1) - B * X ^ 2 + C 10 * (B * X ^ 3) := fun B => by
      simp only [map_ofNat]; ring
    rw [e]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_X,
      coeff_mk]
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> norm_num [show a 0 = 1 by decide, show a 1 = 11 by decide,
        show a 2 = 111 by decide, show a 3 = 1110 by decide]
    · split_ifs <;> first | omega | linarith [P n h]
