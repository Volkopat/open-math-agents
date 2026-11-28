import OMAStatements.S_oeis_a267613

namespace OMA.S_oeis_a267613

open PowerSeries






/-- Barker's conjectures. -/
def Conjecture : Prop :=
  (∀ n : ℕ, 3 < n → (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2)) ∧
  A = (1 - 100 * X + 1010 * X ^ 2 - 900 * X ^ 3) * ((1 - X) * (1 - 100 * X))⁻¹

/-- Rows `n >= 2`: every cell ON except `-n` and `-n+2`. -/
def pat (n : ℕ) : ℤ → Bool := fun x => decide (x ≠ -(n : ℤ) ∧ x ≠ -(n : ℤ) + 2)

theorem state_one : state 185 1 = fun x => decide (x ≠ -1 ∧ x ≠ 0) := by
  funext x
  simp only [state, step]
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ -1 ∧ x ≠ 0 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ -1 ∧ x ≠ 0 by omega)]
    decide

theorem state_two : state 185 2 = pat 2 := by
  funext x
  rw [show state 185 2 = step 185 (state 185 1) from rfl, state_one]
  simp only [step, pat]
  rcases (show x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with
    h | h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ -1 ∧ x - 1 ≠ 0 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 0 by omega),
      decide_eq_true (show x + 1 ≠ -1 ∧ x + 1 ≠ 0 by omega),
      decide_eq_true (show x ≠ -((2 : ℕ) : ℤ) ∧ x ≠ -((2 : ℕ) : ℤ) + 2 by push_cast; omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 ≠ -1 ∧ x - 1 ≠ 0 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 0 by omega),
      decide_eq_true (show x + 1 ≠ -1 ∧ x + 1 ≠ 0 by omega),
      decide_eq_true (show x ≠ -((2 : ℕ) : ℤ) ∧ x ≠ -((2 : ℕ) : ℤ) + 2 by push_cast; omega)]
    decide

theorem step_pat (n : ℕ) : step 185 (pat n) = pat (n + 1) := by
  funext x
  simp only [step, pat]
  push_cast
  set c : ℤ := -(n : ℤ)
  rcases (show x ≤ c - 2 ∨ x = c - 1 ∨ x = c ∨ x = c + 1 ∨ x = c + 2 ∨ x = c + 3 ∨ c + 4 ≤ x by
      omega) with h | h | h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ c ∧ x - 1 ≠ c + 2 by omega),
      decide_eq_true (show x ≠ c ∧ x ≠ c + 2 by omega),
      decide_eq_true (show x + 1 ≠ c ∧ x + 1 ≠ c + 2 by omega),
      decide_eq_true (show x ≠ -((n : ℤ) + 1) ∧ x ≠ -((n : ℤ) + 1) + 2 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ c ∧ x - 1 ≠ c + 2 by omega),
      decide_eq_true (show x ≠ c ∧ x ≠ c + 2 by omega),
      decide_eq_false (show ¬(x + 1 ≠ c ∧ x + 1 ≠ c + 2) by omega),
      decide_eq_false (show ¬(x ≠ -((n : ℤ) + 1) ∧ x ≠ -((n : ℤ) + 1) + 2) by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ c ∧ x - 1 ≠ c + 2 by omega),
      decide_eq_false (show ¬(x ≠ c ∧ x ≠ c + 2) by omega),
      decide_eq_true (show x + 1 ≠ c ∧ x + 1 ≠ c + 2 by omega),
      decide_eq_true (show x ≠ -((n : ℤ) + 1) ∧ x ≠ -((n : ℤ) + 1) + 2 by omega)]
    decide
  · rw [decide_eq_false (show ¬(x - 1 ≠ c ∧ x - 1 ≠ c + 2) by omega),
      decide_eq_true (show x ≠ c ∧ x ≠ c + 2 by omega),
      decide_eq_false (show ¬(x + 1 ≠ c ∧ x + 1 ≠ c + 2) by omega),
      decide_eq_false (show ¬(x ≠ -((n : ℤ) + 1) ∧ x ≠ -((n : ℤ) + 1) + 2) by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ c ∧ x - 1 ≠ c + 2 by omega),
      decide_eq_false (show ¬(x ≠ c ∧ x ≠ c + 2) by omega),
      decide_eq_true (show x + 1 ≠ c ∧ x + 1 ≠ c + 2 by omega),
      decide_eq_true (show x ≠ -((n : ℤ) + 1) ∧ x ≠ -((n : ℤ) + 1) + 2 by omega)]
    decide
  · rw [decide_eq_false (show ¬(x - 1 ≠ c ∧ x - 1 ≠ c + 2) by omega),
      decide_eq_true (show x ≠ c ∧ x ≠ c + 2 by omega),
      decide_eq_true (show x + 1 ≠ c ∧ x + 1 ≠ c + 2 by omega),
      decide_eq_true (show x ≠ -((n : ℤ) + 1) ∧ x ≠ -((n : ℤ) + 1) + 2 by omega)]
    decide
  · rw [decide_eq_true (show x - 1 ≠ c ∧ x - 1 ≠ c + 2 by omega),
      decide_eq_true (show x ≠ c ∧ x ≠ c + 2 by omega),
      decide_eq_true (show x + 1 ≠ c ∧ x + 1 ≠ c + 2 by omega),
      decide_eq_true (show x ≠ -((n : ℤ) + 1) ∧ x ≠ -((n : ℤ) + 1) + 2 by omega)]
    decide

theorem state_ge (n : ℕ) (hn : 2 ≤ n) : state 185 n = pat n := by
  induction n, hn using Nat.le_induction with
  | base => exact state_two
  | succ n hn ih => rw [show state 185 (n + 1) = step 185 (state 185 n) from rfl, ih, step_pat]

theorem geom_ten (k : ℕ) : 9 * ∑ i ∈ Finset.range k, 10 ^ i + 1 = 10 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- `9 a(n) + 1 = 91 * 100^(n-1)` for `n >= 2`. -/
theorem a_ge (n : ℕ) (hn : 2 ≤ n) : 9 * a n + 1 = 91 * 100 ^ (n - 1) := by
  rw [a, rowDigits, state_ge n hn]
  have hsplit : ∀ i ∈ Finset.range (2 * n + 1),
      (pat n ((n : ℤ) - i)).toNat * 10 ^ i + (if i = 2 * n then 10 ^ i else 0) +
        (if i = 2 * n - 2 then 10 ^ i else 0) = 10 ^ i := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases h1 : i = 2 * n
    · rw [if_pos h1, if_neg (by omega), pat,
        decide_eq_false (show ¬((n : ℤ) - (i : ℤ) ≠ -(n : ℤ) ∧ (n : ℤ) - (i : ℤ) ≠ -(n : ℤ) + 2) by
          omega)]
      simp
    · by_cases h2 : i = 2 * n - 2
      · rw [if_neg h1, if_pos h2, pat,
          decide_eq_false (show ¬((n : ℤ) - (i : ℤ) ≠ -(n : ℤ) ∧ (n : ℤ) - (i : ℤ) ≠ -(n : ℤ) + 2) by
            omega)]
        simp
      · rw [if_neg h1, if_neg h2, pat,
          decide_eq_true (show (n : ℤ) - (i : ℤ) ≠ -(n : ℤ) ∧ (n : ℤ) - (i : ℤ) ≠ -(n : ℤ) + 2 by
            omega)]
        simp
  have hs : ∑ i ∈ Finset.range (2 * n + 1),
      ((pat n ((n : ℤ) - i)).toNat * 10 ^ i + (if i = 2 * n then 10 ^ i else 0) +
        (if i = 2 * n - 2 then 10 ^ i else 0)) =
      ∑ i ∈ Finset.range (2 * n + 1), 10 ^ i := Finset.sum_congr rfl hsplit
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (Finset.range (2 * n + 1)) (2 * n),
    Finset.sum_ite_eq' (Finset.range (2 * n + 1)) (2 * n - 2),
    if_pos (Finset.mem_range.2 (by omega)), if_pos (Finset.mem_range.2 (by omega))] at hs
  have hg := geom_ten (2 * n + 1)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h100 : (100 : ℕ) ^ k = 10 ^ (2 * k) := by
    rw [show (100 : ℕ) = 10 ^ 2 by norm_num, ← pow_mul]
  have e1 : (10 : ℕ) ^ (2 * (k + 2) + 1) = 100000 * 10 ^ (2 * k) := by ring
  have e3 : (10 : ℕ) ^ (2 * (k + 2) - 2) = 100 * 10 ^ (2 * k) := by
    rw [show 2 * (k + 2) - 2 = 2 * k + 2 by omega]
    ring
  have e4 : (100 : ℕ) ^ (k + 2 - 1) = 100 * 10 ^ (2 * k) := by
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ, h100]
    ring
  have e5 : (10 : ℕ) ^ (2 * (k + 2)) = 10000 * 10 ^ (2 * k) := by ring
  rw [e1] at hg
  rw [e5, e3] at hs
  rw [e4]
  omega

theorem a_int (n : ℕ) (hn : 2 ≤ n) : 9 * (a n : ℤ) = 91 * 100 ^ (n - 1) - 1 := by
  have h := a_ge n hn
  have h' : ((9 * a n + 1 : ℕ) : ℤ) = ((91 * 100 ^ (n - 1) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linarith

theorem a0 : a 0 = 1 := by decide
theorem a1 : a 1 = 1 := by
  rw [a, rowDigits, state_one]
  decide

theorem recurrence (n : ℕ) (hn : 3 < n) : (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have h1 := a_int (k + 4) (by omega)
  have h2 := a_int (k + 4 - 1) (by omega)
  have h3 := a_int (k + 4 - 2) (by omega)
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 3 - 1 = k + 2 by omega, show k + 2 - 1 = k + 1 by omega] at h1 h2 h3 ⊢
  have key : 9 * ((a (k + 4) : ℤ) - (101 * a (k + 3) - 100 * a (k + 2))) = 0 := by
    linear_combination h1 - 101 * h2 + 100 * h3
  omega

theorem gf_mul : A * ((1 - X) * (1 - 100 * X)) = 1 - 100 * X + 1010 * X ^ 2 - 900 * X ^ 3 := by
  have hD : A * ((1 - X) * (1 - 100 * X)) = A - C 101 * (A * X ^ 1) + C 100 * (A * X ^ 2) := by
    simp only [map_ofNat]
    ring
  have hN : (1 - 100 * X + 1010 * X ^ 2 - 900 * X ^ 3 : ℚ⟦X⟧) =
      C 1 * X ^ 0 - C 100 * X ^ 1 + C 1010 * X ^ 2 - C 900 * X ^ 3 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 4 with hm | hm
  · have e2 : (a 2 : ℚ) = 1011 := by
      have := a_int 2 le_rfl; norm_num at this
      have : (a 2 : ℤ) = 1011 := by linarith
      exact_mod_cast this
    have e3 : (a 3 : ℚ) = 101111 := by
      have := a_int 3 (by norm_num); norm_num at this
      have : (a 3 : ℤ) = 101111 := by linarith
      exact_mod_cast this
    interval_cases m <;> norm_num [a0, a1, e2, e3]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 101 * a (m - 1) - 100 * a (m - 2) := by exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k1 : m - 1 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k3 : m - 3 ≠ 0 := by omega
    simp only [h1, h2, h3, Nat.zero_le, k0, k1, k2, k3, coeff_C, if_true, if_false, hq]
    ring

theorem proof : Conjecture := by
  refine ⟨recurrence, ?_⟩
  have h0 : constantCoeff ((1 - X) * (1 - 100 * X) : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

end OMA.S_oeis_a267613

theorem OMA.solution : type_of% @OMA.S_oeis_a267613.main :=
  OMA.S_oeis_a267613.proof
