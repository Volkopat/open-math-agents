import OMAStatements.S_oeis_a269910

namespace OMA.S_oeis_a269910

open PowerSeries






/-- Barker's conjectures. -/
def Conjecture : Prop :=
  (∀ n : ℕ, (a n : ℤ) =
    -1 + 2 * (-1) ^ n - 2 * (-1 + (-1) ^ n) * n - 2 * (-1 + (-1) ^ n) * n ^ 2) ∧
  (∀ n : ℕ, Even n → a n = 1) ∧
  (∀ n : ℕ, Odd n → (a n : ℤ) = 4 * n ^ 2 + 4 * n - 3) ∧
  (∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6)) ∧
  A = (1 + 5 * X - 2 * X ^ 2 + 30 * X ^ 3 + X ^ 4 - 3 * X ^ 5) * ((1 - X) ^ 3 * (1 + X) ^ 3)⁻¹

/-- Even stages: only the origin is ON. -/
def pE : ℤ × ℤ → Bool := fun p => decide (p.1 = 0 ∧ p.2 = 0)
/-- Odd stages: every cell is ON except the four neighbors of the origin. -/
def pO : ℤ × ℤ → Bool := fun p =>
  decide (¬((p.1 = 1 ∧ p.2 = 0) ∨ (p.1 = -1 ∧ p.2 = 0) ∨ (p.1 = 0 ∧ p.2 = 1) ∨
    (p.1 = 0 ∧ p.2 = -1)))

theorem testBit_three {k : ℕ} (hk : 2 ≤ k) : Nat.testBit 3 k = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk))

theorem step_pE : step 3 pE = pO := by
  funext ⟨x, y⟩
  simp only [step, pE, pO]
  rcases (show (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨
      (x = 0 ∧ y = -1) ∨ (¬(x = 0 ∧ y = 0) ∧ ¬(x = 1 ∧ y = 0) ∧ ¬(x = -1 ∧ y = 0) ∧
      ¬(x = 0 ∧ y = 1) ∧ ¬(x = 0 ∧ y = -1)) by omega) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [decide_eq_false (show ¬(x = 0 ∧ y = 0) by omega),
      decide_eq_false (show ¬(x - 1 = 0 ∧ y = 0) by omega),
      decide_eq_false (show ¬(x + 1 = 0 ∧ y = 0) by omega),
      decide_eq_false (show ¬(x = 0 ∧ y - 1 = 0) by omega),
      decide_eq_false (show ¬(x = 0 ∧ y + 1 = 0) by omega),
      decide_eq_true (show ¬((x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨
        (x = 0 ∧ y = -1)) by omega)]
    decide

theorem step_pO : step 3 pO = pE := by
  funext ⟨x, y⟩
  simp only [step, pE, pO]
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    decide
  · rw [decide_eq_false h0]
    apply testBit_three
    rcases (show 1 ≤ x ∨ x ≤ -1 ∨ (x = 0 ∧ 1 ≤ y) ∨ (x = 0 ∧ y ≤ -1) by omega) with
      h | h | h | h
    · have e : (decide (¬((x + 1 = 1 ∧ y = 0) ∨ (x + 1 = -1 ∧ y = 0) ∨ (x + 1 = 0 ∧ y = 1) ∨
          (x + 1 = 0 ∧ y = -1)))).toNat = 1 := by
        rw [decide_eq_true (by omega)]; rfl
      omega
    · have e : (decide (¬((x - 1 = 1 ∧ y = 0) ∨ (x - 1 = -1 ∧ y = 0) ∨ (x - 1 = 0 ∧ y = 1) ∨
          (x - 1 = 0 ∧ y = -1)))).toNat = 1 := by
        rw [decide_eq_true (by omega)]; rfl
      omega
    · have e : (decide (¬((x = 1 ∧ y + 1 = 0) ∨ (x = -1 ∧ y + 1 = 0) ∨ (x = 0 ∧ y + 1 = 1) ∨
          (x = 0 ∧ y + 1 = -1)))).toNat = 1 := by
        rw [decide_eq_true (by omega)]; rfl
      omega
    · have e : (decide (¬((x = 1 ∧ y - 1 = 0) ∨ (x = -1 ∧ y - 1 = 0) ∨ (x = 0 ∧ y - 1 = 1) ∨
          (x = 0 ∧ y - 1 = -1)))).toNat = 1 := by
        rw [decide_eq_true (by omega)]; rfl
      omega

theorem state_even_odd (k : ℕ) : state 3 (2 * k) = pE ∧ state 3 (2 * k + 1) = pO := by
  induction k with
  | zero =>
    have h0 : state 3 0 = pE := rfl
    exact ⟨h0, by rw [show state 3 (2 * 0 + 1) = step 3 (state 3 0) from rfl, h0, step_pE]⟩
  | succ k ih =>
    have h1 : state 3 (2 * (k + 1)) = pE := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
        show state 3 (2 * k + 1 + 1) = step 3 (state 3 (2 * k + 1)) from rfl, ih.2, step_pO]
    exact ⟨h1, by
      rw [show state 3 (2 * (k + 1) + 1) = step 3 (state 3 (2 * (k + 1))) from rfl, h1, step_pE]⟩

theorem count_pE (n : ℕ) : count pE n = 1 := by
  rw [count]
  have : ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter fun p => pE p = true) =
      {(0, 0)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_singleton,
      Prod.mk.injEq, pE, decide_eq_true_eq]
    omega
  rw [this, Finset.card_singleton]

theorem count_pO (n : ℕ) (hn : 1 ≤ n) : count pO n + 4 = (2 * n + 1) ^ 2 := by
  rw [count]
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n) (fun p => pO p = true)
  have hc : ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
      fun p => ¬ pO p = true) = {(1, 0), (-1, 0), (0, 1), (0, -1)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, pO, decide_eq_true_eq, not_not]
    omega
  have h4 : ({(1, 0), (-1, 0), (0, 1), (0, -1)} : Finset (ℤ × ℤ)).card = 4 := by decide
  rw [hc, h4, Finset.card_product, Int.card_Icc] at h
  have e : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
  rw [e] at h
  rw [sq]
  exact h

theorem a_even (k : ℕ) : a (2 * k) = 1 := by
  rw [a, (state_even_odd k).1, count_pE]

theorem a_odd (k : ℕ) : (a (2 * k + 1) : ℤ) = 4 * (2 * k + 1) ^ 2 + 4 * (2 * k + 1) - 3 := by
  have h := count_pO (2 * k + 1) (by omega)
  rw [← (state_even_odd k).2] at h
  have h' : ((a (2 * k + 1) + 4 : ℕ) : ℤ) = (((2 * (2 * k + 1) + 1) ^ 2 : ℕ) : ℤ) := by
    rw [a]; exact_mod_cast h
  push_cast at h'
  linarith

theorem conj_even (n : ℕ) (hn : Even n) : a n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [show k + k = 2 * k by ring, a_even]

theorem conj_odd (n : ℕ) (hn : Odd n) : (a n : ℤ) = 4 * n ^ 2 + 4 * n - 3 := by
  obtain ⟨k, rfl⟩ := hn
  rw [a_odd]
  push_cast
  ring

theorem conj_closed (n : ℕ) :
    (a n : ℤ) = -1 + 2 * (-1) ^ n - 2 * (-1 + (-1) ^ n) * n - 2 * (-1 + (-1) ^ n) * n ^ 2 := by
  rcases Nat.even_or_odd n with he | ho
  · rw [conj_even n he, Even.neg_one_pow he]
    push_cast
    ring
  · rw [conj_odd n ho, Odd.neg_one_pow ho]
    ring

theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6) := by
  rw [conj_closed n, conj_closed (n - 2), conj_closed (n - 4), conj_closed (n - 6)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  rw [show k + 6 - 2 = k + 4 by omega, show k + 6 - 4 = k + 2 by omega,
    show k + 6 - 6 = k by omega]
  push_cast
  ring

theorem gf_mul : A * ((1 - X) ^ 3 * (1 + X) ^ 3) =
    1 + 5 * X - 2 * X ^ 2 + 30 * X ^ 3 + X ^ 4 - 3 * X ^ 5 := by
  have hD : A * ((1 - X) ^ 3 * (1 + X) ^ 3) =
      A - C 3 * (A * X ^ 2) + C 3 * (A * X ^ 4) - C 1 * (A * X ^ 6) := by
    simp only [map_one, map_ofNat]
    ring
  have hN : (1 + 5 * X - 2 * X ^ 2 + 30 * X ^ 3 + X ^ 4 - 3 * X ^ 5 : ℚ⟦X⟧) =
      C 1 * X ^ 0 + C 5 * X ^ 1 - C 2 * X ^ 2 + C 30 * X ^ 3 + C 1 * X ^ 4 - C 3 * X ^ 5 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hD, hN]
  ext m
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk]
  rcases Nat.lt_or_ge m 6 with hm | hm
  · have e : ∀ j < 6, (a j : ℚ) = [1, 5, 1, 45, 1, 117].getD j 0 := by
      intro j hj
      have := conj_closed j
      have h' : (a j : ℚ) = -1 + 2 * (-1) ^ j - 2 * (-1 + (-1) ^ j) * j -
          2 * (-1 + (-1) ^ j) * j ^ 2 := by exact_mod_cast this
      rw [h']
      interval_cases j <;> norm_num
    have e0 := e 0 (by norm_num)
    have e1 := e 1 (by norm_num)
    have e2 := e 2 (by norm_num)
    have e3 := e 3 (by norm_num)
    have e4 := e 4 (by norm_num)
    have e5 := e 5 (by norm_num)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at e0 e1 e2 e3 e4 e5
    interval_cases m <;> norm_num [e0, e1, e2, e3, e4, e5]
  · have hr := recurrence m (by omega)
    have hq : (a m : ℚ) = 3 * a (m - 2) - 3 * a (m - 4) + a (m - 6) := by exact_mod_cast hr
    have h1 : 1 ≤ m := by omega
    have h2 : 2 ≤ m := by omega
    have h3 : 3 ≤ m := by omega
    have h4 : 4 ≤ m := by omega
    have h5 : 5 ≤ m := by omega
    have h6 : 6 ≤ m := by omega
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
  refine ⟨conj_closed, conj_even, conj_odd, recurrence, ?_⟩
  have h0 : constantCoeff ((1 - X) ^ 3 * (1 + X) ^ 3 : ℚ⟦X⟧) ≠ 0 := by simp
  rw [← gf_mul, mul_assoc, PowerSeries.mul_inv_cancel _ h0, mul_one]

end OMA.S_oeis_a269910

theorem OMA.solution : type_of% @OMA.S_oeis_a269910.main :=
  OMA.S_oeis_a269910.proof
