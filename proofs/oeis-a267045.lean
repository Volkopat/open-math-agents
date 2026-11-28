import OMAStatements.S_oeis_a267045

/-!
# A267045: the middle column of Rule 91, read in base 2

Rule 91 turns a cell ON when its two neighbours differ, or when all three cells are OFF. From
stage 3 on the pattern has period 2: at odd stages exactly the cells `-1, 0, 1` are OFF, at even
stages exactly the cells `-2, ..., 2` are ON. So the middle cell of stage `n + 3` is ON exactly
when `n` is odd.
-/

namespace OMA.S_oeis_a267045

open PowerSeries

lemma eca_iff (l c r : Bool) : eca 91 l c r = true ↔
    ¬(l = true ↔ r = true) ∨ ¬(l = true ∨ c = true ∨ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_iff (t : ℕ) : ∀ i : ℤ, state (t + 3) i = true ↔
    t % 2 = 0 ∧ (i < -1 ∨ 1 < i) ∨ t % 2 = 1 ∧ -2 ≤ i ∧ i ≤ 2 := by
  have r2 : ∀ i : ℤ, state 2 i = true ↔ i = -1 ∨ i = 1 := fun i => by
    simp only [state, eca_iff, decide_eq_true_eq]; omega
  induction t with
  | zero => intro i; show state 3 i = true ↔ _; rw [state, eca_iff, r2, r2, r2]; omega
  | succ t ih => intro i; rw [state, eca_iff]; simp only [ih]; omega

lemma a_step (n : ℕ) : (2 * a (n + 3) : ℤ) = 4 * a (n + 2) + 1 - (-1) ^ n := by
  have h : a (n + 3) = 2 * a (n + 2) + if state (n + 3) 0 then 1 else 0 := by
    unfold a
    rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Nat.succ_sub (Finset.mem_range_succ_iff.mp ht), pow_succ']
    split_ifs <;> rfl
  rw [h, neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · rw [if_neg fun h => by have := (state_iff n 0).1 h; omega, e]; push_cast; ring
  · rw [if_pos ((state_iff n 0).2 (by omega)), e]; push_cast; ring

end OMA.S_oeis_a267045

open OMA.S_oeis_a267045 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267045.main := by
  have K : ∀ n, 12 * (a (n + 2) : ℤ) = 2 * (-1) ^ n + 52 * 2 ^ n - 6 := fun n => by
    induction n with
    | zero => norm_num [show a 2 = 4 by decide]
    | succ n ih => rw [pow_succ, pow_succ]; linarith [a_step n]
  have P : ∀ n, 4 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) := fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h1 : (2 * a (m + 5) : ℤ) = 4 * a (m + 4) + 1 - (-1) ^ (m + 2) := a_step (m + 2)
    rw [pow_succ, pow_succ] at h1
    show (a (m + 5) : ℤ) = 2 * a (m + 4) + a (m + 3) - 2 * a (m + 2)
    linarith [a_step m]
  refine ⟨fun n hn => ?_, P, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [K m]; ring
  · have e : ∀ B : ℤ⟦X⟧, B * ((1 - X) * (1 + X) * (1 - 2 * X)) =
        B - C 2 * (B * X ^ 1) - B * X ^ 2 + C 2 * (B * X ^ 3) := fun B => by
      simp only [map_ofNat]; ring
    rw [e]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_one, coeff_mk]
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> norm_num [show a 0 = 1 by decide, show a 1 = 2 by decide,
        show a 2 = 4 by decide, show a 3 = 8 by decide, show a 4 = 17 by decide]
    · split_ifs <;> first | omega | linarith [P n h]
