import OMAStatements.S_oeis_a266607

namespace OMA.S_oeis_a266607

open PowerSeries






/-- Barker's conjectures. -/
def Conjecture : Prop :=
  (∀ n : ℕ, 5 < n → (a n : ℤ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6)) ∧
  A = (1 + 6 * X - 17 * X ^ 2 + 11 * X ^ 3 + 16 * X ^ 4 - 32 * X ^ 5) *
    ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2))⁻¹

/-- Even rows: one ON cell, at `m`. -/
def pE (m : ℕ) : ℤ → Bool := fun x => decide (x = m)
/-- Odd rows: every cell ON except cell `m + 1`. -/
def pO (m : ℕ) : ℤ → Bool := fun x => decide (x ≠ m + 1)

theorem step_pE (m : ℕ) : step 39 (pE m) = pO m := by
  funext x
  simp only [step, pE, pO]
  rcases (show x ≤ (m : ℤ) - 2 ∨ x = m - 1 ∨ x = m ∨ x = m + 1 ∨ (m : ℤ) + 2 ≤ x by omega) with
    h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ m by omega), decide_eq_false (show x ≠ m by omega),
      decide_eq_false (show x + 1 ≠ m by omega), decide_eq_true (show x ≠ m + 1 by omega)]
    decide
  · rw [decide_eq_false (show x - 1 ≠ m by omega), decide_eq_false (show x ≠ m by omega),
      decide_eq_true (show x + 1 = m by omega), decide_eq_true (show x ≠ m + 1 by omega)]
    decide
  · rw [decide_eq_false (show x - 1 ≠ m by omega), decide_eq_true (show x = m by omega),
      decide_eq_false (show x + 1 ≠ m by omega), decide_eq_true (show x ≠ m + 1 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 = m by omega), decide_eq_false (show x ≠ m by omega),
      decide_eq_false (show x + 1 ≠ m by omega), decide_eq_false (show ¬(x ≠ m + 1) by omega)]
    decide
  · rw [decide_eq_false (show x - 1 ≠ m by omega), decide_eq_false (show x ≠ m by omega),
      decide_eq_false (show x + 1 ≠ m by omega), decide_eq_true (show x ≠ m + 1 by omega)]
    decide

theorem step_pO (m : ℕ) : step 39 (pO m) = pE (m + 1) := by
  funext x
  simp only [step, pE, pO]
  push_cast
  rcases (show x ≤ (m : ℤ) - 1 ∨ x = m ∨ x = m + 1 ∨ x = m + 2 ∨ (m : ℤ) + 3 ≤ x by omega) with
    h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ m + 1 by omega), decide_eq_true (show x ≠ m + 1 by omega),
      decide_eq_true (show x + 1 ≠ m + 1 by omega), decide_eq_false (show x ≠ m + 1 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ m + 1 by omega), decide_eq_true (show x ≠ m + 1 by omega),
      decide_eq_false (show ¬(x + 1 ≠ m + 1) by omega), decide_eq_false (show x ≠ m + 1 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ m + 1 by omega),
      decide_eq_false (show ¬(x ≠ m + 1) by omega),
      decide_eq_true (show x + 1 ≠ m + 1 by omega), decide_eq_true (show x = m + 1 by omega)]
    decide
  · rw [decide_eq_false (show ¬(x - 1 ≠ m + 1) by omega),
      decide_eq_true (show x ≠ m + 1 by omega),
      decide_eq_true (show x + 1 ≠ m + 1 by omega), decide_eq_false (show x ≠ m + 1 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ m + 1 by omega), decide_eq_true (show x ≠ m + 1 by omega),
      decide_eq_true (show x + 1 ≠ m + 1 by omega), decide_eq_false (show x ≠ m + 1 by omega)]
    decide

theorem state_even_odd (m : ℕ) : state 39 (2 * m) = pE m ∧ state 39 (2 * m + 1) = pO m := by
  induction m with
  | zero =>
    have h0 : state 39 0 = pE 0 := by funext x; simp [state, pE]
    refine ⟨h0, ?_⟩
    rw [show state 39 (2 * 0 + 1) = step 39 (state 39 0) from rfl, h0, step_pE]
  | succ m ih =>
    have h1 : state 39 (2 * (m + 1)) = pE (m + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
        show state 39 (2 * m + 1 + 1) = step 39 (state 39 (2 * m + 1)) from rfl, ih.2, step_pO]
    refine ⟨h1, ?_⟩
    rw [show state 39 (2 * (m + 1) + 1) = step 39 (state 39 (2 * (m + 1))) from rfl, h1, step_pE]

theorem geom_two (k : ℕ) : ∑ i ∈ Finset.range k, 2 ^ i + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem a_even (m : ℕ) : a (2 * m) = 2 ^ m := by
  rw [a, (state_even_odd m).1, rowValue]
  have hsplit : ∀ i ∈ Finset.range (2 * (2 * m) + 1),
      (pE m (((2 * m : ℕ) : ℤ) - i)).toNat * 2 ^ i = if i = m then 2 ^ i else 0 := by
    intro i hi
    by_cases h : i = m
    · rw [if_pos h, pE, decide_eq_true (show ((2 * m : ℕ) : ℤ) - (i : ℤ) = m by push_cast; omega)]
      simp
    · rw [if_neg h, pE, decide_eq_false (show ((2 * m : ℕ) : ℤ) - (i : ℤ) ≠ m by push_cast; omega)]
      simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_ite_eq' (Finset.range (2 * (2 * m) + 1)) m,
    if_pos (Finset.mem_range.2 (by omega))]

theorem a_odd (m : ℕ) : a (2 * m + 1) + 2 ^ m + 1 = 2 ^ (4 * m + 3) := by
  rw [a, (state_even_odd m).2, rowValue]
  have hsplit : ∀ i ∈ Finset.range (2 * (2 * m + 1) + 1),
      (pO m (((2 * m + 1 : ℕ) : ℤ) - i)).toNat * 2 ^ i + (if i = m then 2 ^ i else 0) =
        2 ^ i := by
    intro i hi
    by_cases h : i = m
    · rw [if_pos h, pO,
        decide_eq_false (show ¬(((2 * m + 1 : ℕ) : ℤ) - (i : ℤ) ≠ m + 1) by push_cast; omega)]
      simp
    · rw [if_neg h, pO,
        decide_eq_true (show ((2 * m + 1 : ℕ) : ℤ) - (i : ℤ) ≠ m + 1 by push_cast; omega)]
      simp
  have hs : ∑ i ∈ Finset.range (2 * (2 * m + 1) + 1),
      ((pO m (((2 * m + 1 : ℕ) : ℤ) - i)).toNat * 2 ^ i + (if i = m then 2 ^ i else 0)) =
      ∑ i ∈ Finset.range (2 * (2 * m + 1) + 1), 2 ^ i := Finset.sum_congr rfl hsplit
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (2 * (2 * m + 1) + 1)) m,
    if_pos (Finset.mem_range.2 (by omega))] at hs
  have hg := geom_two (2 * (2 * m + 1) + 1)
  rw [show (2 : ℕ) ^ (2 * (2 * m + 1) + 1) = 2 ^ (4 * m + 3) by ring_nf] at hg
  omega

theorem a_odd_int (m : ℕ) : (a (2 * m + 1) : ℤ) = 2 ^ (4 * m + 3) - 1 - 2 ^ m := by
  have h := a_odd m
  have h' : ((a (2 * m + 1) + 2 ^ m + 1 : ℕ) : ℤ) = ((2 ^ (4 * m + 3) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    rw [hm, show j + 3 + (j + 3) - 2 = 2 * (j + 2) by omega,
      show j + 3 + (j + 3) - 4 = 2 * (j + 1) by omega, show j + 3 + (j + 3) - 6 = 2 * j by omega,
      show j + 3 + (j + 3) = 2 * (j + 3) by omega, a_even, a_even, a_even, a_even]
    push_cast
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    rw [hm, show 2 * (j + 3) + 1 - 2 = 2 * (j + 2) + 1 by omega,
      show 2 * (j + 3) + 1 - 4 = 2 * (j + 1) + 1 by omega,
      show 2 * (j + 3) + 1 - 6 = 2 * j + 1 by omega, a_odd_int, a_odd_int, a_odd_int, a_odd_int]
    ring

theorem gf_mul : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) =
    1 + 6 * X - 17 * X ^ 2 + 11 * X ^ 3 + 16 * X ^ 4 - 32 * X ^ 5 := by
  have hD : A * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2)) =
      A - C 19 * (A * X ^ 2) + C 50 * (A * X ^ 4) - C 32 * (A * X ^ 6) := by
    simp only [map_ofNat]
    ring
  have hN : (1 + 6 * X - 17 * X ^ 2 + 11 * X ^ 3 + 16 * X ^ 4 - 32 * X ^ 5 : ℚ⟦X⟧) =
      C 1 * X ^ 0 + C 6 * X ^ 1 - C 17 * X ^ 2 + C 11 * X ^ 3 + C 16 * X ^ 4 - C 32 * X ^ 5 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 6 with hm | hm
  · have e0 : (a 0 : ℚ) = 1 := by have := a_even 0; norm_num at this; exact_mod_cast this
    have e2 : (a 2 : ℚ) = 2 := by have := a_even 1; norm_num at this; exact_mod_cast this
    have e4 : (a 4 : ℚ) = 4 := by have := a_even 2; norm_num at this; exact_mod_cast this
    have e1 : (a 1 : ℚ) = 6 := by
      have := a_odd_int 0; norm_num at this; exact_mod_cast this
    have e3 : (a 3 : ℚ) = 125 := by
      have := a_odd_int 1; norm_num at this; exact_mod_cast this
    have e5 : (a 5 : ℚ) = 2043 := by
      have := a_odd_int 2; norm_num at this; exact_mod_cast this
    interval_cases m <;> norm_num [e0, e1, e2, e3, e4, e5]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 19 * a (m - 2) - 50 * a (m - 4) + 32 * a (m - 6) := by
      exact_mod_cast hr
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
    simp only [h1, h2, h3, h4, h5, h6, Nat.zero_le, k0, k1, k2, k3, k4, k5, coeff_C, if_true,
      if_false, hq]
    ring

theorem proof : Conjecture := by
  refine ⟨recurrence, ?_⟩
  have h0 : constantCoeff ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2) :
      ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

/-- Control: the first terms listed in the entry. -/
theorem a_values : a 0 = 1 ∧ a 1 = 6 ∧ a 2 = 2 ∧ a 3 = 125 ∧ a 4 = 4 ∧ a 5 = 2043 ∧
    a 6 = 8 ∧ a 7 = 32759 := by
  have o0 := a_odd 0
  have o1 := a_odd 1
  have o2 := a_odd 2
  have o3 := a_odd 3
  have e0 := a_even 0
  have e1 := a_even 1
  have e2 := a_even 2
  have e3 := a_even 3
  norm_num at o0 o1 o2 o3 e0 e1 e2 e3
  omega

end OMA.S_oeis_a266607

theorem OMA.solution : type_of% @OMA.S_oeis_a266607.main :=
  OMA.S_oeis_a266607.proof
