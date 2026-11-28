import OMAStatements.S_oeis_a266718

namespace OMA.S_oeis_a266718

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

theorem geom_two (k : ℕ) : ∑ i ∈ Finset.range k, 2 ^ i + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem a_zero : a 0 = 1 := by
  simp [a, rowValue, state]

theorem a_odd (k : ℕ) : a (2 * k + 1) + 2 ^ (k + 1) + 1 = 2 ^ (4 * k + 3) := by
  rw [a, (state_odd_even k).1, rowValue]
  have hsplit : ∀ i ∈ Finset.range (2 * (2 * k + 1) + 1),
      (pO k (((2 * k + 1 : ℕ) : ℤ) - i)).toNat * 2 ^ i + (if i = k + 1 then 2 ^ i else 0) =
        2 ^ i := by
    intro i hi
    by_cases h : i = k + 1
    · rw [if_pos h, pO,
        decide_eq_false (show ¬(((2 * k + 1 : ℕ) : ℤ) - (i : ℤ) ≠ k) by push_cast; omega)]
      simp
    · rw [if_neg h, pO,
        decide_eq_true (show ((2 * k + 1 : ℕ) : ℤ) - (i : ℤ) ≠ k by push_cast; omega)]
      simp
  have hs : ∑ i ∈ Finset.range (2 * (2 * k + 1) + 1),
      ((pO k (((2 * k + 1 : ℕ) : ℤ) - i)).toNat * 2 ^ i + (if i = k + 1 then 2 ^ i else 0)) =
      ∑ i ∈ Finset.range (2 * (2 * k + 1) + 1), 2 ^ i := Finset.sum_congr rfl hsplit
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (2 * (2 * k + 1) + 1)) (k + 1),
    if_pos (Finset.mem_range.2 (by omega))] at hs
  have hg := geom_two (2 * (2 * k + 1) + 1)
  rw [show (2 : ℕ) ^ (2 * (2 * k + 1) + 1) = 2 ^ (4 * k + 3) by ring_nf] at hg
  omega

theorem a_even (k : ℕ) : a (2 * k + 2) = 3 * 2 ^ (k + 1) := by
  rw [a, (state_odd_even k).2, rowValue]
  have hsplit : ∀ i ∈ Finset.range (2 * (2 * k + 2) + 1),
      (pE (k + 1) (((2 * k + 2 : ℕ) : ℤ) - i)).toNat * 2 ^ i =
        (if i = k + 1 then 2 ^ i else 0) + (if i = k + 2 then 2 ^ i else 0) := by
    intro i hi
    by_cases h1 : i = k + 1
    · rw [if_pos h1, if_neg (by omega), pE,
        decide_eq_true (show ((2 * k + 2 : ℕ) : ℤ) - (i : ℤ) = ((k + 1 : ℕ) : ℤ) - 1 ∨
          ((2 * k + 2 : ℕ) : ℤ) - (i : ℤ) = ((k + 1 : ℕ) : ℤ) by push_cast; omega)]
      simp
    · by_cases h2 : i = k + 2
      · rw [if_neg h1, if_pos h2, pE,
          decide_eq_true (show ((2 * k + 2 : ℕ) : ℤ) - (i : ℤ) = ((k + 1 : ℕ) : ℤ) - 1 ∨
            ((2 * k + 2 : ℕ) : ℤ) - (i : ℤ) = ((k + 1 : ℕ) : ℤ) by push_cast; omega)]
        simp
      · rw [if_neg h1, if_neg h2, pE,
          decide_eq_false (show ¬(((2 * k + 2 : ℕ) : ℤ) - (i : ℤ) = ((k + 1 : ℕ) : ℤ) - 1 ∨
            ((2 * k + 2 : ℕ) : ℤ) - (i : ℤ) = ((k + 1 : ℕ) : ℤ)) by push_cast; omega)]
        simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range (2 * (2 * k + 2) + 1)) (k + 1),
    Finset.sum_ite_eq' (Finset.range (2 * (2 * k + 2) + 1)) (k + 2),
    if_pos (Finset.mem_range.2 (by omega)), if_pos (Finset.mem_range.2 (by omega))]
  ring

theorem a_odd_q (k : ℕ) : (a (2 * k + 1) : ℚ) = 2 ^ (4 * k + 3) - 1 - 2 ^ (k + 1) := by
  have h := a_odd k
  have h' : ((a (2 * k + 1) + 2 ^ (k + 1) + 1 : ℕ) : ℚ) = ((2 ^ (4 * k + 3) : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  linarith

theorem a_even_q (k : ℕ) : (a (2 * k + 2) : ℚ) = 3 * 2 ^ (k + 1) := by
  rw [a_even]; push_cast; ring

theorem recurrence_q (n : ℕ) (hn : 6 < n) :
    (a n : ℚ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 4 := ⟨m - 4, by omega⟩
    rw [hm, show j + 4 + (j + 4) - 2 = 2 * (j + 2) + 2 by omega,
      show j + 4 + (j + 4) - 4 = 2 * (j + 1) + 2 by omega,
      show j + 4 + (j + 4) - 6 = 2 * j + 2 by omega,
      show j + 4 + (j + 4) = 2 * (j + 3) + 2 by omega, a_even_q, a_even_q, a_even_q, a_even_q]
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    rw [hm, show 2 * (j + 3) + 1 - 2 = 2 * (j + 2) + 1 by omega,
      show 2 * (j + 3) + 1 - 4 = 2 * (j + 1) + 1 by omega,
      show 2 * (j + 3) + 1 - 6 = 2 * j + 1 by omega, a_odd_q, a_odd_q, a_odd_q, a_odd_q]
    ring

theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6) := by
  have h := recurrence_q n hn
  exact_mod_cast h

theorem gf_mul : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) =
    (1 - 2 * X) * (1 + 7 * X + X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 - 32 * X ^ 5) := by
  have hD : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) =
      A - C 19 * (A * X ^ 2) + C 50 * (A * X ^ 4) - C 32 * (A * X ^ 6) := by
    simp only [map_ofNat]
    ring
  have hN : ((1 - 2 * X) * (1 + 7 * X + X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 - 32 * X ^ 5) : ℚ⟦X⟧) =
      C 1 * X ^ 0 + C 5 * X ^ 1 - C 13 * X ^ 2 + C 28 * X ^ 3 - C 52 * X ^ 4 - C 48 * X ^ 5 +
        C 64 * X ^ 6 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 7 with hm | hm
  · have e0 : (a 0 : ℚ) = 1 := by rw [a_zero]; norm_num
    have e2 : (a 2 : ℚ) = 6 := by have := a_even_q 0; norm_num at this; exact_mod_cast this
    have e4 : (a 4 : ℚ) = 12 := by have := a_even_q 1; norm_num at this; exact_mod_cast this
    have e6 : (a 6 : ℚ) = 24 := by have := a_even_q 2; norm_num at this; exact_mod_cast this
    have e1 : (a 1 : ℚ) = 5 := by have := a_odd_q 0; norm_num at this; exact_mod_cast this
    have e3 : (a 3 : ℚ) = 123 := by have := a_odd_q 1; norm_num at this; exact_mod_cast this
    have e5 : (a 5 : ℚ) = 2039 := by have := a_odd_q 2; norm_num at this; exact_mod_cast this
    interval_cases m <;> norm_num [e0, e1, e2, e3, e4, e5, e6]
  · have hq := recurrence_q m (by omega)
    have h2 : 2 ≤ m := by omega
    have h4 : 4 ≤ m := by omega
    have h6 : 6 ≤ m := by omega
    have h1 : 1 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have h5 : 5 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k1 : m - 1 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k3 : m - 3 ≠ 0 := by omega
    have k4 : m - 4 ≠ 0 := by omega
    have k5 : m - 5 ≠ 0 := by omega
    have k6 : m - 6 ≠ 0 := by omega
    simp only [h1, h2, h3, h4, h5, h6, Nat.zero_le, k0, k1, k2, k3, k4, k5, k6, coeff_C, if_true,
      if_false, hq]
    ring

/-- Barker's two conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6)) ∧
    A = (1 - 2 * X) * (1 + 7 * X + X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 - 32 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2))⁻¹ := by
  refine ⟨recurrence, ?_⟩
  have h0 : constantCoeff ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2) :
      ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

/-- Controls: the entry's terms a(0..14). -/
theorem controls : a 0 = 1 ∧ a 1 = 5 ∧ a 2 = 6 ∧ a 3 = 123 ∧ a 4 = 12 ∧ a 5 = 2039 ∧
    a 6 = 24 ∧ a 7 = 32751 ∧ a 8 = 48 ∧ a 9 = 524255 ∧ a 10 = 96 ∧ a 11 = 8388543 ∧
    a 12 = 192 ∧ a 13 = 134217599 ∧ a 14 = 384 := by
  have o0 := a_odd 0
  have o1 := a_odd 1
  have o2 := a_odd 2
  have o3 := a_odd 3
  have o4 := a_odd 4
  have o5 := a_odd 5
  have o6 := a_odd 6
  have e0 := a_even 0
  have e1 := a_even 1
  have e2 := a_even 2
  have e3 := a_even 3
  have e4 := a_even 4
  have e5 := a_even 5
  have e6 := a_even 6
  norm_num at o0 o1 o2 o3 o4 o5 o6 e0 e1 e2 e3 e4 e5 e6
  exact ⟨a_zero, by omega, e0, by omega, e1, by omega, e2, by omega, e3, by omega, e4, by omega,
    e5, by omega, e6⟩

end OMA.S_oeis_a266718

theorem OMA.solution : type_of% @OMA.S_oeis_a266718.main :=
  OMA.S_oeis_a266718.conjecture
