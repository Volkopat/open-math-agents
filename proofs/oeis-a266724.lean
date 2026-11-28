import OMAStatements.S_oeis_a266724

namespace OMA.S_oeis_a266724

open PowerSeries






/-- Odd rows: every cell ON except cell `k`. -/
def pO (k : ℕ) : ℤ → Bool := fun x => decide (x ≠ k)
/-- Even rows from row 2 on: the cells `j - 1` and `j` ON, all others OFF. -/
def pE (j : ℕ) : ℤ → Bool := fun x => decide (x = (j : ℤ) - 1 ∨ x = j)

theorem step_zero : step 59 (state 59 0) = pO 0 := by
  funext x
  simp only [step, state, pO]
  push_cast
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 0 by omega)]
    decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_true (show x + 1 = 0 by omega), decide_eq_true (show x ≠ 0 by omega)]
    decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_true (show x = 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_false (show ¬(x ≠ 0) by omega)]
    decide
  · rw [decide_eq_true (show x - 1 = 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 0 by omega)]
    decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ 0 by omega)]
    decide

theorem step_pO (k : ℕ) : step 59 (pO k) = pE (k + 1) := by
  funext x
  simp only [step, pE, pO]
  push_cast
  rcases (show x ≤ (k : ℤ) - 2 ∨ x = k - 1 ∨ x = k ∨ x = k + 1 ∨ (k : ℤ) + 2 ≤ x by omega) with
    h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ k by omega), decide_eq_true (show x ≠ k by omega),
      decide_eq_true (show x + 1 ≠ k by omega),
      decide_eq_false (show ¬(x = (k : ℤ) + 1 - 1 ∨ x = k + 1) by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ k by omega), decide_eq_true (show x ≠ k by omega),
      decide_eq_false (show ¬(x + 1 ≠ k) by omega),
      decide_eq_false (show ¬(x = (k : ℤ) + 1 - 1 ∨ x = k + 1) by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ k by omega), decide_eq_false (show ¬(x ≠ k) by omega),
      decide_eq_true (show x + 1 ≠ k by omega),
      decide_eq_true (show x = (k : ℤ) + 1 - 1 ∨ x = k + 1 by omega)]
    decide
  · rw [decide_eq_false (show ¬(x - 1 ≠ k) by omega), decide_eq_true (show x ≠ k by omega),
      decide_eq_true (show x + 1 ≠ k by omega),
      decide_eq_true (show x = (k : ℤ) + 1 - 1 ∨ x = k + 1 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ k by omega), decide_eq_true (show x ≠ k by omega),
      decide_eq_true (show x + 1 ≠ k by omega),
      decide_eq_false (show ¬(x = (k : ℤ) + 1 - 1 ∨ x = k + 1) by omega)]
    decide

theorem step_pE (j : ℕ) : step 59 (pE j) = pO j := by
  funext x
  simp only [step, pE, pO]
  rcases (show x ≤ (j : ℤ) - 3 ∨ x = j - 2 ∨ x = j - 1 ∨ x = j ∨ x = j + 1 ∨ (j : ℤ) + 2 ≤ x by
      omega) with h | h | h | h | h | h
  · rw [decide_eq_false (show ¬(x - 1 = (j : ℤ) - 1 ∨ x - 1 = j) by omega),
      decide_eq_false (show ¬(x = (j : ℤ) - 1 ∨ x = j) by omega),
      decide_eq_false (show ¬(x + 1 = (j : ℤ) - 1 ∨ x + 1 = j) by omega),
      decide_eq_true (show x ≠ j by omega)]
    decide
  · rw [decide_eq_false (show ¬(x - 1 = (j : ℤ) - 1 ∨ x - 1 = j) by omega),
      decide_eq_false (show ¬(x = (j : ℤ) - 1 ∨ x = j) by omega),
      decide_eq_true (show x + 1 = (j : ℤ) - 1 ∨ x + 1 = j by omega),
      decide_eq_true (show x ≠ j by omega)]
    decide
  · rw [decide_eq_false (show ¬(x - 1 = (j : ℤ) - 1 ∨ x - 1 = j) by omega),
      decide_eq_true (show x = (j : ℤ) - 1 ∨ x = j by omega),
      decide_eq_true (show x + 1 = (j : ℤ) - 1 ∨ x + 1 = j by omega),
      decide_eq_true (show x ≠ j by omega)]
    decide
  · rw [decide_eq_true (show x - 1 = (j : ℤ) - 1 ∨ x - 1 = j by omega),
      decide_eq_true (show x = (j : ℤ) - 1 ∨ x = j by omega),
      decide_eq_false (show ¬(x + 1 = (j : ℤ) - 1 ∨ x + 1 = j) by omega),
      decide_eq_false (show ¬(x ≠ j) by omega)]
    decide
  · rw [decide_eq_true (show x - 1 = (j : ℤ) - 1 ∨ x - 1 = j by omega),
      decide_eq_false (show ¬(x = (j : ℤ) - 1 ∨ x = j) by omega),
      decide_eq_false (show ¬(x + 1 = (j : ℤ) - 1 ∨ x + 1 = j) by omega),
      decide_eq_true (show x ≠ j by omega)]
    decide
  · rw [decide_eq_false (show ¬(x - 1 = (j : ℤ) - 1 ∨ x - 1 = j) by omega),
      decide_eq_false (show ¬(x = (j : ℤ) - 1 ∨ x = j) by omega),
      decide_eq_false (show ¬(x + 1 = (j : ℤ) - 1 ∨ x + 1 = j) by omega),
      decide_eq_true (show x ≠ j by omega)]
    decide

theorem state_odd_even (k : ℕ) :
    state 59 (2 * k + 1) = pO k ∧ state 59 (2 * k + 2) = pE (k + 1) := by
  induction k with
  | zero =>
    have h1 : state 59 (2 * 0 + 1) = pO 0 := step_zero
    refine ⟨h1, ?_⟩
    rw [show state 59 (2 * 0 + 2) = step 59 (state 59 (2 * 0 + 1)) from rfl, h1, step_pO]
  | succ k ih =>
    have h1 : state 59 (2 * (k + 1) + 1) = pO (k + 1) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 2 + 1 by ring,
        show state 59 (2 * k + 2 + 1) = step 59 (state 59 (2 * k + 2)) from rfl, ih.2, step_pE]
    refine ⟨h1, ?_⟩
    rw [show state 59 (2 * (k + 1) + 2) = step 59 (state 59 (2 * (k + 1) + 1)) from rfl, h1,
      step_pO]

theorem a_zero : a 0 = 0 := by
  simp [a, offCount, state]

theorem a_odd (k : ℕ) : a (2 * k + 1) = 1 := by
  rw [a, (state_odd_even k).1, offCount, Finset.card_eq_one]
  refine ⟨k + 1, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, pO,
    decide_eq_false_iff_not, not_not]
  push_cast
  omega

theorem a_even (k : ℕ) : a (2 * k + 2) = 4 * k + 3 := by
  rw [a, (state_odd_even k).2, offCount]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range (2 * (2 * k + 2) + 1))
    (fun i : ℕ => pE (k + 1) (((2 * k + 2 : ℕ) : ℤ) - i) = false)
  have h2 : (Finset.range (2 * (2 * k + 2) + 1)).filter
      (fun i : ℕ => ¬ (pE (k + 1) (((2 * k + 2 : ℕ) : ℤ) - i) = false)) = {k + 1, k + 2} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, pE,
      decide_eq_false_iff_not, not_not]
    push_cast
    omega
  rw [h2, Finset.card_pair (by omega), Finset.card_range] at h
  omega

theorem a_odd_z (k : ℕ) : (a (2 * k + 1) : ℤ) = 1 := by
  rw [a_odd]; norm_num

theorem a_even_z (k : ℕ) : (a (2 * k + 2) : ℤ) = 4 * k + 3 := by
  rw [a_even]; push_cast; ring

theorem closed_form (n : ℕ) (hn : 0 < n) : (a n : ℤ) = (-1) ^ n * ((n : ℤ) - 1) + n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [hm, show j + 1 + (j + 1) = 2 * j + 2 by omega, a_even_z,
      show 2 * j + 2 = 2 * (j + 1) by omega, pow_mul]
    push_cast
    ring
  · rw [hm, a_odd_z, pow_succ, pow_mul]
    push_cast
    ring

theorem recurrence (n : ℕ) (hn : 4 < n) : (a n : ℤ) = 2 * a (n - 2) - a (n - 4) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    rw [hm, show j + 3 + (j + 3) - 2 = 2 * (j + 1) + 2 by omega,
      show j + 3 + (j + 3) - 4 = 2 * j + 2 by omega,
      show j + 3 + (j + 3) = 2 * (j + 2) + 2 by omega, a_even_z, a_even_z, a_even_z]
    push_cast
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    rw [hm, show 2 * (j + 2) + 1 - 2 = 2 * (j + 1) + 1 by omega,
      show 2 * (j + 2) + 1 - 4 = 2 * j + 1 by omega, a_odd_z, a_odd_z, a_odd_z]
    norm_num

theorem gf_mul : A * ((1 - X) ^ 2 * (1 + X) ^ 2) = X * (1 + 3 * X - X ^ 2 + X ^ 3) := by
  have hD : A * ((1 - X) ^ 2 * (1 + X) ^ 2) = A - C 2 * (A * X ^ 2) + A * X ^ 4 := by
    simp only [map_ofNat]
    ring
  have hN : (X * (1 + 3 * X - X ^ 2 + X ^ 3) : ℚ⟦X⟧) =
      C 1 * X ^ 1 + C 3 * X ^ 2 - C 1 * X ^ 3 + C 1 * X ^ 4 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · have e0 : (a 0 : ℚ) = 0 := by rw [a_zero]; norm_num
    have e1 : (a 1 : ℚ) = 1 := by have := a_odd 0; norm_num at this; exact_mod_cast this
    have e3 : (a 3 : ℚ) = 1 := by have := a_odd 1; norm_num at this; exact_mod_cast this
    have e2 : (a 2 : ℚ) = 3 := by have := a_even 0; norm_num at this; exact_mod_cast this
    have e4 : (a 4 : ℚ) = 7 := by have := a_even 1; norm_num at this; exact_mod_cast this
    interval_cases m <;> norm_num [e0, e1, e2, e3, e4]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 2 * a (m - 2) - a (m - 4) := by exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have h4 : 4 ≤ m := by omega
    have k1 : m - 1 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k3 : m - 3 ≠ 0 := by omega
    have k4 : m - 4 ≠ 0 := by omega
    simp only [h1, h2, h3, h4, k1, k2, k3, k4, coeff_C, if_true, if_false, hq]
    ring

/-- Barker's three conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 0 < n → (a n : ℤ) = (-1) ^ n * ((n : ℤ) - 1) + n) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) ∧
    A = X * (1 + 3 * X - X ^ 2 + X ^ 3) * ((1 - X) ^ 2 * (1 + X) ^ 2)⁻¹ := by
  refine ⟨closed_form, recurrence, ?_⟩
  have h0 : constantCoeff ((1 - X) ^ 2 * (1 + X) ^ 2 : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

/-- Controls: the entry's terms a(0..15). -/
theorem controls : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 1 ∧ a 4 = 7 ∧ a 5 = 1 ∧ a 6 = 11 ∧
    a 7 = 1 ∧ a 8 = 15 ∧ a 9 = 1 ∧ a 10 = 19 ∧ a 11 = 1 ∧ a 12 = 23 ∧ a 13 = 1 ∧ a 14 = 27 ∧
    a 15 = 1 :=
  ⟨a_zero, a_odd 0, a_even 0, a_odd 1, a_even 1, a_odd 2, a_even 2, a_odd 3, a_even 3, a_odd 4,
    a_even 4, a_odd 5, a_even 5, a_odd 6, a_even 6, a_odd 7⟩

end OMA.S_oeis_a266724

theorem OMA.solution : type_of% @OMA.S_oeis_a266724.main :=
  OMA.S_oeis_a266724.conjecture
