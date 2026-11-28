import OMAStatements.S_oeis_a266723

namespace OMA.S_oeis_a266723

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

theorem on_zero : onCount (state 59 0) 0 = 1 := by decide

theorem on_odd (k : ℕ) : onCount (state 59 (2 * k + 1)) (2 * k + 1) = 4 * k + 2 := by
  rw [(state_odd_even k).1, onCount]
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range (2 * (2 * k + 1) + 1))
    (fun i : ℕ => pO k (((2 * k + 1 : ℕ) : ℤ) - i) = true)
  have h2 : (Finset.range (2 * (2 * k + 1) + 1)).filter
      (fun i : ℕ => ¬ (pO k (((2 * k + 1 : ℕ) : ℤ) - i) = true)) = {k + 1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, pO,
      decide_eq_true_eq, not_not]
    push_cast
    omega
  rw [h2, Finset.card_singleton, Finset.card_range] at h
  omega

theorem on_even (k : ℕ) : onCount (state 59 (2 * k + 2)) (2 * k + 2) = 2 := by
  rw [(state_odd_even k).2, onCount, Finset.card_eq_two]
  refine ⟨k + 1, k + 2, by omega, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, pE,
    decide_eq_true_eq]
  push_cast
  omega

theorem a_succ (n : ℕ) : a (n + 1) = a n + onCount (state 59 (n + 1)) (n + 1) :=
  Finset.sum_range_succ _ _

theorem a_parity (m : ℕ) : a (2 * m) = 2 * m ^ 2 + 2 * m + 1 ∧
    a (2 * m + 1) = 2 * m ^ 2 + 6 * m + 3 := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · show ∑ t ∈ Finset.range 1, onCount (state 59 t) t = 1
      rw [Finset.sum_range_one, on_zero]
    · rw [a_succ, show 0 + 1 = 2 * 0 + 1 by rfl, on_odd 0]
      show ∑ t ∈ Finset.range 1, onCount (state 59 t) t + 2 = 3
      rw [Finset.sum_range_one, on_zero]
  | succ m ih =>
    have e1 : a (2 * (m + 1)) = 2 * (m + 1) ^ 2 + 2 * (m + 1) + 1 := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, a_succ, ih.2,
        show 2 * m + 1 + 1 = 2 * m + 2 by ring, on_even m]
      ring
    refine ⟨e1, ?_⟩
    rw [a_succ, e1, on_odd (m + 1)]
    ring

/-- Barker's closed form, multiplied out: 4 a(n) = 3 + (-1)^n - 2(-3 + (-1)^n) n + 2n^2. -/
theorem closed (n : ℕ) :
    4 * (a n : ℤ) = 3 + (-1) ^ n - 2 * (-3 + (-1) ^ n) * n + 2 * n ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [(a_parity m).1, (even_two_mul m).neg_one_pow]
    push_cast
    ring
  · rw [(a_parity m).2, (odd_two_mul_add_one m).neg_one_pow]
    push_cast
    ring

/-- Barker's recurrence, for n > 4. -/
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega]
  have e5 := closed (m + 5)
  have e4 := closed (m + 4)
  have e3 := closed (m + 3)
  have e2 := closed (m + 2)
  have e1 := closed (m + 1)
  have e0 := closed m
  rcases Nat.even_or_odd m with h | h
  · have h1 : Odd (m + 1) := h.add_one
    have h2 : Even (m + 2) := h1.add_one
    have h3 : Odd (m + 3) := h2.add_one
    have h4 : Even (m + 4) := h3.add_one
    have h5 : Odd (m + 5) := h4.add_one
    rw [h5.neg_one_pow] at e5; rw [h4.neg_one_pow] at e4; rw [h3.neg_one_pow] at e3
    rw [h2.neg_one_pow] at e2; rw [h1.neg_one_pow] at e1; rw [h.neg_one_pow] at e0
    push_cast at e5 e4 e3 e2 e1 e0
    linarith
  · have h1 : Even (m + 1) := h.add_one
    have h2 : Odd (m + 2) := h1.add_one
    have h3 : Even (m + 3) := h2.add_one
    have h4 : Odd (m + 4) := h3.add_one
    have h5 : Even (m + 5) := h4.add_one
    rw [h5.neg_one_pow] at e5; rw [h4.neg_one_pow] at e4; rw [h3.neg_one_pow] at e3
    rw [h2.neg_one_pow] at e2; rw [h1.neg_one_pow] at e1; rw [h.neg_one_pow] at e0
    push_cast at e5 e4 e3 e2 e1 e0
    linarith

/-- Barker's generating function, as an identity of formal power series. -/
theorem gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
    (1 + 2 * X - X ^ 2) * (1 + X ^ 2) := by
  have hD : ((1 - X) ^ 3 * (1 + X) ^ 2 : ℤ⟦X⟧) =
      1 - X ^ 1 - (X ^ 2 + X ^ 2) + (X ^ 3 + X ^ 3) + X ^ 4 - X ^ 5 := by ring
  have hN : ((1 + 2 * X - X ^ 2) * (1 + X ^ 2) : ℤ⟦X⟧) =
      1 + (X ^ 1 + X ^ 1) + (X ^ 3 + X ^ 3) - X ^ 4 := by ring
  rw [hD, hN]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_mk,
    coeff_X_pow, coeff_one]
  have v : ∀ k, (a k : ℤ) = (3 + (-1) ^ k - 2 * (-3 + (-1) ^ k) * k + 2 * k ^ 2) / 4 := by
    intro k; have := closed k; omega
  rcases Nat.lt_or_ge n 5 with hn | hn
  · have h0 : (a 0 : ℤ) = 1 := by rw [v]; norm_num
    have h1 : (a 1 : ℤ) = 3 := by rw [v]; norm_num
    have h2 : (a 2 : ℤ) = 5 := by rw [v]; norm_num
    have h3 : (a 3 : ℤ) = 11 := by rw [v]; norm_num
    have h4 : (a 4 : ℤ) = 13 := by rw [v]; norm_num
    interval_cases n <;> simp [h0, h1, h2, h3, h4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have := recurrence (m + 5) (by omega)
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
      show m + 5 - 5 = m by omega] at this
    rw [if_pos (show 1 ≤ m + 5 by omega), if_pos (show 2 ≤ m + 5 by omega),
      if_pos (show 3 ≤ m + 5 by omega), if_pos (show 4 ≤ m + 5 by omega),
      if_pos (show 5 ≤ m + 5 by omega),
      show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
      show m + 5 - 5 = m by omega]
    rw [if_neg (show ¬ (m + 5 = 0) by omega), if_neg (show ¬ (m + 5 = 1) by omega),
      if_neg (show ¬ (m + 5 = 3) by omega), if_neg (show ¬ (m + 5 = 4) by omega)]
    linarith

/-- Controls: the entry's terms a(0..15). -/
theorem controls : a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 5 ∧ a 3 = 11 ∧ a 4 = 13 ∧ a 5 = 23 ∧ a 6 = 25 ∧
    a 7 = 39 ∧ a 8 = 41 ∧ a 9 = 59 ∧ a 10 = 61 ∧ a 11 = 83 ∧ a 12 = 85 ∧ a 13 = 111 ∧
    a 14 = 113 ∧ a 15 = 143 :=
  ⟨(a_parity 0).1, (a_parity 0).2, (a_parity 1).1, (a_parity 1).2, (a_parity 2).1,
    (a_parity 2).2, (a_parity 3).1, (a_parity 3).2, (a_parity 4).1, (a_parity 4).2,
    (a_parity 5).1, (a_parity 5).2, (a_parity 6).1, (a_parity 6).2, (a_parity 7).1,
    (a_parity 7).2⟩

/-- Barker's three conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 4 * (a n : ℤ) = 3 + (-1) ^ n - 2 * (-3 + (-1) ^ n) * n + 2 * n ^ 2) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      (1 + 2 * X - X ^ 2) * (1 + X ^ 2) :=
  ⟨closed, recurrence, gf⟩

end OMA.S_oeis_a266723

theorem OMA.solution : type_of% @OMA.S_oeis_a266723.main :=
  OMA.S_oeis_a266723.conjecture
