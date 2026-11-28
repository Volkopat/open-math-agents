import OMAStatements.S_oeis_a266594

namespace OMA.S_oeis_a266594

open PowerSeries






/-- Barker's conjectures. -/
def Conjecture : Prop :=
  (∀ n : ℕ, 0 < n → (a n : ℚ) = ((n : ℚ) ^ 2 - (-1) ^ n * ((n : ℚ) - 3) + 5) / 2) ∧
  (∀ n : ℕ, 5 < n →
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
  A = (1 + X + X ^ 2 - 2 * X ^ 4 + 3 * X ^ 5) * ((1 - X) ^ 3 * (1 + X) ^ 2)⁻¹

/-- Even rows from row 2 on: ON exactly on `[-1, 1]`. -/
def pE : ℤ → Bool := fun x => decide (-1 ≤ x ∧ x ≤ 1)
/-- Odd rows from row 3 on: OFF exactly on `[-2, 2]`. -/
def pO : ℤ → Bool := fun x => decide (x < -2 ∨ 2 < x)

theorem state_one : state 37 1 = fun x => decide (x ≠ -1 ∧ x ≠ 1) := by
  funext x
  simp only [state, step]
  rcases (show x ≤ -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ 2 ≤ x by omega) with h | h | h | h | h
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ -1 ∧ x ≠ 1 by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show x - 1 ≠ 0 by omega), decide_eq_false (show x ≠ 0 by omega),
      decide_eq_false (show x + 1 ≠ 0 by omega), decide_eq_true (show x ≠ -1 ∧ x ≠ 1 by omega)]
    decide

theorem state_two : state 37 2 = pE := by
  funext x
  rw [show state 37 2 = step 37 (state 37 1) from rfl, state_one]
  simp only [step, pE]
  rcases (show x ≤ -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ 3 ≤ x by omega) with
    h | h | h | h | h | h | h
  · rw [decide_eq_true (show x - 1 ≠ -1 ∧ x - 1 ≠ 1 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 1 by omega),
      decide_eq_true (show x + 1 ≠ -1 ∧ x + 1 ≠ 1 by omega),
      decide_eq_false (show ¬(-1 ≤ x ∧ x ≤ 1) by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 ≠ -1 ∧ x - 1 ≠ 1 by omega),
      decide_eq_true (show x ≠ -1 ∧ x ≠ 1 by omega),
      decide_eq_true (show x + 1 ≠ -1 ∧ x + 1 ≠ 1 by omega),
      decide_eq_false (show ¬(-1 ≤ x ∧ x ≤ 1) by omega)]
    decide

theorem step_pE : step 37 pE = pO := by
  funext x
  simp only [step, pO, pE]
  rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by
      omega) with h | h | h | h | h | h | h | h | h
  · rw [decide_eq_false (show ¬(-1 ≤ x - 1 ∧ x - 1 ≤ 1) by omega),
      decide_eq_false (show ¬(-1 ≤ x ∧ x ≤ 1) by omega),
      decide_eq_false (show ¬(-1 ≤ x + 1 ∧ x + 1 ≤ 1) by omega),
      decide_eq_true (show x < -2 ∨ 2 < x by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_false (show ¬(-1 ≤ x - 1 ∧ x - 1 ≤ 1) by omega),
      decide_eq_false (show ¬(-1 ≤ x ∧ x ≤ 1) by omega),
      decide_eq_false (show ¬(-1 ≤ x + 1 ∧ x + 1 ≤ 1) by omega),
      decide_eq_true (show x < -2 ∨ 2 < x by omega)]
    decide

theorem step_pO : step 37 pO = pE := by
  funext x
  simp only [step, pO, pE]
  rcases (show x ≤ -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by
      omega) with h | h | h | h | h | h | h | h | h
  · rw [decide_eq_true (show x - 1 < -2 ∨ 2 < x - 1 by omega),
      decide_eq_true (show x < -2 ∨ 2 < x by omega),
      decide_eq_true (show x + 1 < -2 ∨ 2 < x + 1 by omega),
      decide_eq_false (show ¬(-1 ≤ x ∧ x ≤ 1) by omega)]
    decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · subst h; decide
  · rw [decide_eq_true (show x - 1 < -2 ∨ 2 < x - 1 by omega),
      decide_eq_true (show x < -2 ∨ 2 < x by omega),
      decide_eq_true (show x + 1 < -2 ∨ 2 < x + 1 by omega),
      decide_eq_false (show ¬(-1 ≤ x ∧ x ≤ 1) by omega)]
    decide

theorem state_late (k : ℕ) : state 37 (2 * k + 2) = pE ∧ state 37 (2 * k + 3) = pO := by
  induction k with
  | zero =>
    refine ⟨state_two, ?_⟩
    rw [show state 37 (2 * 0 + 3) = step 37 (state 37 2) from rfl, state_two, step_pE]
  | succ k ih =>
    have h1 : state 37 (2 * (k + 1) + 2) = pE := by
      rw [show 2 * (k + 1) + 2 = 2 * k + 3 + 1 by ring,
        show state 37 (2 * k + 3 + 1) = step 37 (state 37 (2 * k + 3)) from rfl, ih.2, step_pO]
    refine ⟨h1, ?_⟩
    rw [show state 37 (2 * (k + 1) + 3) = step 37 (state 37 (2 * (k + 1) + 2)) from rfl, h1,
      step_pE]

theorem count_pE (k : ℕ) (hk : 1 ≤ k) : rowCount pE k = 3 := by
  rw [rowCount]
  have : ((Finset.Icc (-(k : ℤ)) k).filter fun x => pE x = true) = Finset.Icc (-1) 1 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, pE, decide_eq_true_eq]
    omega
  rw [this]
  rfl

theorem count_pO (k : ℕ) (hk : 2 ≤ k) : rowCount pO k + 5 = 2 * k + 1 := by
  rw [rowCount]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.Icc (-(k : ℤ)) k)
    (fun x => pO x = true)
  have hc : ((Finset.Icc (-(k : ℤ)) k).filter fun x => ¬ pO x = true) = Finset.Icc (-2) 2 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, pO, decide_eq_true_eq]
    omega
  rw [hc, Int.card_Icc, Int.card_Icc] at h
  have e1 : ((2 : ℤ) + 1 - -2).toNat = 5 := by decide
  have e2 : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
  rw [e1, e2] at h
  exact h

theorem a_succ (n : ℕ) : a (n + 1) = a n + rowCount (state 37 (n + 1)) (n + 1) := by
  rw [a, a, Finset.sum_range_succ]

theorem a0 : a 0 = 1 := by
  rw [a, Finset.sum_range_one, rowCount]
  have : ((Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).filter fun x => state 37 0 x = true) =
      {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, state,
      decide_eq_true_eq]
    omega
  rw [this, Finset.card_singleton]

theorem a1 : a 1 = 2 := by
  rw [a_succ, a0, state_one, rowCount]
  have : ((Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).filter
      fun x => decide (x ≠ -1 ∧ x ≠ 1) = true) = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, decide_eq_true_eq]
    omega
  rw [this, Finset.card_singleton]

/-- `2 a(n) = n^2 - (-1)^n (n - 3) + 5` for `n >= 1`. -/
theorem closed (n : ℕ) (hn : 1 ≤ n) :
    2 * (a n : ℤ) = (n : ℤ) ^ 2 - (-1) ^ n * ((n : ℤ) - 3) + 5 := by
  induction n, hn using Nat.le_induction with
  | base => rw [a1]; norm_num
  | succ n hn ih =>
    rw [a_succ]
    push_cast
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- n even, n + 1 = 2m + 1 odd, with m >= 1
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have hs : state 37 (n + 1) = pO := by
        rw [show n + 1 = 2 * j + 3 by omega]; exact (state_late j).2
      have hc := count_pO (n + 1) (by omega)
      rw [hs]
      have q0 : ((-1 : ℤ)) ^ n = 1 := Even.neg_one_pow ⟨_, hm⟩
      have q1 : ((-1 : ℤ)) ^ (n + 1) = -1 := by rw [pow_succ, q0]; ring
      rw [q1]
      rw [q0] at ih
      have hc' : ((rowCount pO (n + 1) : ℕ) : ℤ) + 5 = 2 * ((n : ℤ) + 1) + 1 := by
        exact_mod_cast hc
      push_cast at hc' ⊢
      linarith
    · -- n odd, n + 1 = 2m + 2 even
      have hs : state 37 (n + 1) = pE := by
        rw [show n + 1 = 2 * m + 2 by omega]; exact (state_late m).1
      have hc := count_pE (n + 1) (by omega)
      rw [hs, hc]
      have q0 : ((-1 : ℤ)) ^ n = -1 := Odd.neg_one_pow ⟨_, hm⟩
      have q1 : ((-1 : ℤ)) ^ (n + 1) = 1 := by rw [pow_succ, q0]; ring
      rw [q1]
      rw [q0] at ih
      push_cast
      linarith

theorem barker_closed (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = ((n : ℚ) ^ 2 - (-1) ^ n * ((n : ℚ) - 3) + 5) / 2 := by
  have h := closed n hn
  have h' : (2 : ℚ) * (a n : ℚ) = (n : ℚ) ^ 2 - (-1) ^ n * ((n : ℚ) - 3) + 5 := by
    exact_mod_cast h
  rw [eq_div_iff (by norm_num)]
  linarith

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have h0 := closed (k + 6) (by omega)
  have h1 := closed (k + 5) (by omega)
  have h2 := closed (k + 4) (by omega)
  have h3 := closed (k + 3) (by omega)
  have h4 := closed (k + 2) (by omega)
  have h5 := closed (k + 1) (by omega)
  rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
    show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
    show k + 6 - 5 = k + 1 by omega]
  push_cast at h0 h1 h2 h3 h4 h5
  have key : 2 * ((a (k + 6) : ℤ) - (a (k + 5) + 2 * a (k + 4) - 2 * a (k + 3) - a (k + 2) +
      a (k + 1))) = 0 := by
    linear_combination h0 - h1 - 2 * h2 + 2 * h3 + h4 - h5
  omega

theorem gf_mul : A * ((1 - X) ^ 3 * (1 + X) ^ 2) = 1 + X + X ^ 2 - 2 * X ^ 4 + 3 * X ^ 5 := by
  have hD : A * ((1 - X) ^ 3 * (1 + X) ^ 2) = A - C 1 * (A * X ^ 1) - C 2 * (A * X ^ 2) +
      C 2 * (A * X ^ 3) + C 1 * (A * X ^ 4) - C 1 * (A * X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hN : (1 + X + X ^ 2 - 2 * X ^ 4 + 3 * X ^ 5 : ℚ⟦X⟧) =
      C 1 * X ^ 0 + C 1 * X ^ 1 + C 1 * X ^ 2 - C 2 * X ^ 4 + C 3 * X ^ 5 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 6 with hm | hm
  · have e2 : (a 2 : ℚ) = 5 := by
      have := barker_closed 2 (by norm_num); norm_num at this; exact this
    have e3 : (a 3 : ℚ) = 7 := by
      have := barker_closed 3 (by norm_num); norm_num at this; exact this
    have e4 : (a 4 : ℚ) = 10 := by
      have := barker_closed 4 (by norm_num); norm_num at this; exact this
    have e5 : (a 5 : ℚ) = 16 := by
      have := barker_closed 5 (by norm_num); norm_num at this; exact this
    interval_cases m <;> norm_num [a0, a1, e2, e3, e4, e5]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = a (m - 1) + 2 * a (m - 2) - 2 * a (m - 3) - a (m - 4) + a (m - 5) := by
      exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have h4 : 4 ≤ m := by omega
    have h5 : 5 ≤ m := by omega
    have k0 : m - 0 ≠ 0 := by omega
    have k1 : m - 1 ≠ 0 := by omega
    have k2 : m - 2 ≠ 0 := by omega
    have k4 : m - 4 ≠ 0 := by omega
    have k5 : m - 5 ≠ 0 := by omega
    simp only [h1, h2, h3, h4, h5, Nat.zero_le, k0, k1, k2, k4, k5, coeff_C, if_true, if_false,
      hq]
    ring

theorem proof : Conjecture := by
  refine ⟨barker_closed, recurrence, ?_⟩
  have h0 : constantCoeff ((1 - X) ^ 3 * (1 + X) ^ 2 : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

end OMA.S_oeis_a266594

theorem OMA.solution : type_of% @OMA.S_oeis_a266594.main :=
  OMA.S_oeis_a266594.proof
