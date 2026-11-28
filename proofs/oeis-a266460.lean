import OMAStatements.S_oeis_a266460

namespace OMA.S_oeis_a266460

open PowerSeries






/-- Even rows: one ON cell, at `m`. -/
def pE (m : ℕ) : ℤ → Bool := fun x => decide (x = m)
/-- Odd rows: every cell ON except cell `m`. -/
def pO (m : ℕ) : ℤ → Bool := fun x => decide (x ≠ m)

theorem step_pE (m : ℕ) : step 27 (pE m) = pO m := by
  funext x
  simp only [step, pE, pO]
  rcases (show x ≤ (m : ℤ) - 2 ∨ x = m - 1 ∨ x = m ∨ x = m + 1 ∨ (m : ℤ) + 2 ≤ x by omega) with
    h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ m by omega), decide_eq_false (show x ≠ m by omega),
      decide_eq_false (show x + 1 ≠ m by omega), decide_eq_true (show x ≠ m by omega)]
    decide
  · rw [decide_eq_false (show x - 1 ≠ m by omega), decide_eq_false (show x ≠ m by omega),
      decide_eq_true (show x + 1 = m by omega), decide_eq_true (show x ≠ m by omega)]
    decide
  · rw [decide_eq_false (show x - 1 ≠ m by omega), decide_eq_true (show x = m by omega),
      decide_eq_false (show x + 1 ≠ m by omega), decide_eq_false (show ¬(x ≠ m) by omega)]
    decide
  · rw [decide_eq_true (show x - 1 = m by omega), decide_eq_false (show x ≠ m by omega),
      decide_eq_false (show x + 1 ≠ m by omega), decide_eq_true (show x ≠ m by omega)]
    decide
  · rw [decide_eq_false (show x - 1 ≠ m by omega), decide_eq_false (show x ≠ m by omega),
      decide_eq_false (show x + 1 ≠ m by omega), decide_eq_true (show x ≠ m by omega)]
    decide

theorem step_pO (m : ℕ) : step 27 (pO m) = pE (m + 1) := by
  funext x
  simp only [step, pE, pO]
  push_cast
  rcases (show x ≤ (m : ℤ) - 2 ∨ x = m - 1 ∨ x = m ∨ x = m + 1 ∨ (m : ℤ) + 2 ≤ x by omega) with
    h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ m by omega), decide_eq_true (show x ≠ m by omega),
      decide_eq_true (show x + 1 ≠ m by omega), decide_eq_false (show x ≠ m + 1 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ m by omega), decide_eq_true (show x ≠ m by omega),
      decide_eq_false (show ¬(x + 1 ≠ m) by omega), decide_eq_false (show x ≠ m + 1 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ m by omega), decide_eq_false (show ¬(x ≠ m) by omega),
      decide_eq_true (show x + 1 ≠ m by omega), decide_eq_false (show x ≠ m + 1 by omega)]
    decide
  · rw [decide_eq_false (show ¬(x - 1 ≠ m) by omega), decide_eq_true (show x ≠ m by omega),
      decide_eq_true (show x + 1 ≠ m by omega), decide_eq_true (show x = m + 1 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ m by omega), decide_eq_true (show x ≠ m by omega),
      decide_eq_true (show x + 1 ≠ m by omega), decide_eq_false (show x ≠ m + 1 by omega)]
    decide

theorem state_even_odd (m : ℕ) : state 27 (2 * m) = pE m ∧ state 27 (2 * m + 1) = pO m := by
  induction m with
  | zero =>
    have h0 : state 27 0 = pE 0 := by funext x; simp [state, pE]
    refine ⟨h0, ?_⟩
    rw [show state 27 (2 * 0 + 1) = step 27 (state 27 0) from rfl, h0, step_pE]
  | succ m ih =>
    have h1 : state 27 (2 * (m + 1)) = pE (m + 1) := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
        show state 27 (2 * m + 1 + 1) = step 27 (state 27 (2 * m + 1)) from rfl, ih.2, step_pO]
    refine ⟨h1, ?_⟩
    rw [show state 27 (2 * (m + 1) + 1) = step 27 (state 27 (2 * (m + 1))) from rfl, h1, step_pE]

theorem geom_ten (k : ℕ) : 9 * ∑ i ∈ Finset.range k, 10 ^ i + 1 = 10 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem a_even (m : ℕ) : a (2 * m) = 10 ^ m := by
  rw [a, (state_even_odd m).1, rowDigits]
  have hsplit : ∀ i ∈ Finset.range (2 * (2 * m) + 1),
      (pE m (((2 * m : ℕ) : ℤ) - i)).toNat * 10 ^ i = if i = m then 10 ^ i else 0 := by
    intro i hi
    by_cases h : i = m
    · rw [if_pos h, pE, decide_eq_true (show ((2 * m : ℕ) : ℤ) - (i : ℤ) = m by push_cast; omega)]
      simp
    · rw [if_neg h, pE, decide_eq_false (show ((2 * m : ℕ) : ℤ) - (i : ℤ) ≠ m by push_cast; omega)]
      simp
  rw [Finset.sum_congr rfl hsplit, Finset.sum_ite_eq' (Finset.range (2 * (2 * m) + 1)) m,
    if_pos (Finset.mem_range.2 (by omega))]

theorem a_odd (m : ℕ) : 9 * a (2 * m + 1) + 9 * 10 ^ (m + 1) + 1 = 10 ^ (4 * m + 3) := by
  rw [a, (state_even_odd m).2, rowDigits]
  have hsplit : ∀ i ∈ Finset.range (2 * (2 * m + 1) + 1),
      (pO m (((2 * m + 1 : ℕ) : ℤ) - i)).toNat * 10 ^ i + (if i = m + 1 then 10 ^ i else 0) =
        10 ^ i := by
    intro i hi
    by_cases h : i = m + 1
    · rw [if_pos h, pO,
        decide_eq_false (show ¬(((2 * m + 1 : ℕ) : ℤ) - (i : ℤ) ≠ m) by push_cast; omega)]
      simp
    · rw [if_neg h, pO,
        decide_eq_true (show ((2 * m + 1 : ℕ) : ℤ) - (i : ℤ) ≠ m by push_cast; omega)]
      simp
  have hs : ∑ i ∈ Finset.range (2 * (2 * m + 1) + 1),
      ((pO m (((2 * m + 1 : ℕ) : ℤ) - i)).toNat * 10 ^ i + (if i = m + 1 then 10 ^ i else 0)) =
      ∑ i ∈ Finset.range (2 * (2 * m + 1) + 1), 10 ^ i := Finset.sum_congr rfl hsplit
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (2 * (2 * m + 1) + 1)) (m + 1),
    if_pos (Finset.mem_range.2 (by omega))] at hs
  have hg := geom_ten (2 * (2 * m + 1) + 1)
  rw [show (10 : ℕ) ^ (2 * (2 * m + 1) + 1) = 10 ^ (4 * m + 3) by ring_nf] at hg
  omega

theorem a_odd_q (m : ℕ) : (a (2 * m + 1) : ℚ) = (10 ^ (4 * m + 3) - 1) / 9 - 10 ^ (m + 1) := by
  have h := a_odd m
  have h' : ((9 * a (2 * m + 1) + 9 * 10 ^ (m + 1) + 1 : ℕ) : ℚ) = ((10 ^ (4 * m + 3) : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  linarith

theorem a_even_q (m : ℕ) : (a (2 * m) : ℚ) = 10 ^ m := by
  rw [a_even]; push_cast; ring

theorem recurrence_q (n : ℕ) (hn : 5 < n) :
    (a n : ℚ) = 10011 * a (n - 2) - 110010 * a (n - 4) + 100000 * a (n - 6) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    rw [hm, show j + 3 + (j + 3) - 2 = 2 * (j + 2) by omega,
      show j + 3 + (j + 3) - 4 = 2 * (j + 1) by omega, show j + 3 + (j + 3) - 6 = 2 * j by omega,
      show j + 3 + (j + 3) = 2 * (j + 3) by omega, a_even_q, a_even_q, a_even_q, a_even_q]
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    rw [hm, show 2 * (j + 3) + 1 - 2 = 2 * (j + 2) + 1 by omega,
      show 2 * (j + 3) + 1 - 4 = 2 * (j + 1) + 1 by omega,
      show 2 * (j + 3) + 1 - 6 = 2 * j + 1 by omega, a_odd_q, a_odd_q, a_odd_q, a_odd_q]
    ring

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 10011 * a (n - 2) - 110010 * a (n - 4) + 100000 * a (n - 6) := by
  have h := recurrence_q n hn
  exact_mod_cast h

theorem keller_odd (n : ℕ) (hn : Odd n) :
    (a n : ℚ) = (10 * (100 ^ n - 9 * 10 ^ (n / 2)) - 1) / 9 := by
  obtain ⟨m, rfl⟩ := hn
  rw [a_odd_q, show (2 * m + 1) / 2 = m by omega]
  rw [show (100 : ℚ) = 10 ^ 2 by norm_num, ← pow_mul]
  ring

theorem keller_even (n : ℕ) (hn : Even n) : a n = 10 ^ (n / 2) := by
  obtain ⟨m, rfl⟩ := hn
  rw [show m + m = 2 * m by ring, a_even, show 2 * m / 2 = m by omega]

theorem gf_mul : A * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 10 * X ^ 2)) =
    1 + 101 * X - 10001 * X ^ 2 + 99900 * X ^ 3 + 10000 * X ^ 4 - 110000 * X ^ 5 := by
  have hD : A * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 10 * X ^ 2)) =
      A - C 10011 * (A * X ^ 2) + C 110010 * (A * X ^ 4) - C 100000 * (A * X ^ 6) := by
    simp only [map_ofNat]
    ring
  have hN : (1 + 101 * X - 10001 * X ^ 2 + 99900 * X ^ 3 + 10000 * X ^ 4 - 110000 * X ^ 5 :
      ℚ⟦X⟧) = C 1 * X ^ 0 + C 101 * X ^ 1 - C 10001 * X ^ 2 + C 99900 * X ^ 3 +
        C 10000 * X ^ 4 - C 110000 * X ^ 5 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 6 with hm | hm
  · have e0 : (a 0 : ℚ) = 1 := by have := a_even_q 0; norm_num at this; exact_mod_cast this
    have e2 : (a 2 : ℚ) = 10 := by have := a_even_q 1; norm_num at this; exact_mod_cast this
    have e4 : (a 4 : ℚ) = 100 := by have := a_even_q 2; norm_num at this; exact_mod_cast this
    have e1 : (a 1 : ℚ) = 101 := by have := a_odd_q 0; norm_num at this; exact_mod_cast this
    have e3 : (a 3 : ℚ) = 1111011 := by
      have := a_odd_q 1; norm_num at this; exact_mod_cast this
    have e5 : (a 5 : ℚ) = 11111110111 := by
      have := a_odd_q 2; norm_num at this; exact_mod_cast this
    interval_cases m <;> norm_num [e0, e1, e2, e3, e4, e5]
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
    simp only [h1, h2, h3, h4, h5, h6, Nat.zero_le, k0, k1, k2, k3, k4, k5, coeff_C, if_true,
      if_false, hq]
    ring

/-- Barker's two conjectures and Keller's closed form. -/
theorem conjecture :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 10011 * a (n - 2) - 110010 * a (n - 4) + 100000 * a (n - 6)) ∧
    A = (1 + 101 * X - 10001 * X ^ 2 + 99900 * X ^ 3 + 10000 * X ^ 4 - 110000 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 10 * X ^ 2))⁻¹ ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = (10 * (100 ^ n - 9 * 10 ^ (n / 2)) - 1) / 9) ∧
    (∀ n : ℕ, Even n → a n = 10 ^ (n / 2)) := by
  refine ⟨recurrence, ?_, keller_odd, keller_even⟩
  have h0 : constantCoeff ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 10 * X ^ 2) :
      ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

/-- Controls: the entry's terms a(0..9). -/
theorem controls : a 0 = 1 ∧ a 1 = 101 ∧ a 2 = 10 ∧ a 3 = 1111011 ∧ a 4 = 100 ∧
    a 5 = 11111110111 ∧ a 6 = 1000 ∧ a 7 = 111111111101111 ∧ a 8 = 10000 ∧
    a 9 = 1111111111111011111 := by
  have o0 := a_odd 0
  have o1 := a_odd 1
  have o2 := a_odd 2
  have o3 := a_odd 3
  have o4 := a_odd 4
  have e0 := a_even 0
  have e1 := a_even 1
  have e2 := a_even 2
  have e3 := a_even 3
  have e4 := a_even 4
  norm_num at o0 o1 o2 o3 o4 e0 e1 e2 e3 e4
  omega

end OMA.S_oeis_a266460

theorem OMA.solution : type_of% @OMA.S_oeis_a266460.main :=
  OMA.S_oeis_a266460.conjecture
