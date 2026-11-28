import OMAStatements.S_oeis_a284354

namespace OMA.S_oeis_a284354

open PowerSeries



theorem testBit899 (k : ℕ) :
    Nat.testBit 899 k = decide (k = 0 ∨ k = 1 ∨ k = 7 ∨ k = 8 ∨ k = 9) := by
  rcases Nat.lt_or_ge k 10 with h | h
  · interval_cases k <;> decide
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num : 899 < 2 ^ 10)
      (Nat.pow_le_pow_right (by norm_num) h))]
    simp; omega

theorem step (t : ℕ) (P Q : ℤ → ℤ → Prop) [∀ x y, Decidable (P x y)] [∀ x y, Decidable (Q x y)]
    (hP : ∀ x y, state t x y = decide (P x y))
    (hQ : ∀ x y, (Q x y ↔ (let k := (if P x y then 1 else 0) + 2 * ((if P (x - 1) y then 1 else 0)
      + (if P (x + 1) y then 1 else 0) + (if P x (y - 1) then 1 else 0)
      + (if P x (y + 1) then 1 else 0)); k = 0 ∨ k = 1 ∨ k = 7 ∨ k = 8 ∨ k = 9))) :
    ∀ x y, state (t + 1) x y = decide (Q x y) := by
  intro x y
  show Nat.testBit 899 _ = _
  rw [testBit899, hP, hP, hP, hP, hP]
  apply Bool.decide_congr
  rw [hQ]
  simp only [Bool.toNat, decide_eq_true_eq, cond_eq_if]

def P0 (x y : ℤ) : Prop := x = 0 ∧ y = 0
/-- Odd stages: OFF exactly at the four neighbors of the origin. -/
def PO (x y : ℤ) : Prop := ¬ ((x = 0 ∧ (y = 1 ∨ y = -1)) ∨ (y = 0 ∧ (x = 1 ∨ x = -1)))
/-- Even stages `t ≥ 2`: OFF exactly at the four diagonal neighbors. -/
def PE (x y : ℤ) : Prop := ¬ ((x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1))

instance (x y : ℤ) : Decidable (P0 x y) := by unfold P0; infer_instance
instance (x y : ℤ) : Decidable (PO x y) := by unfold PO; infer_instance
instance (x y : ℤ) : Decidable (PE x y) := by unfold PE; infer_instance

theorem stage1 : ∀ x y, state 1 x y = decide (PO x y) := by
  apply step 0 P0 PO (fun x y => rfl)
  intro x y
  by_cases h1 : P0 x y <;> by_cases h2 : P0 (x - 1) y <;> by_cases h3 : P0 (x + 1) y <;>
    by_cases h4 : P0 x (y - 1) <;> by_cases h5 : P0 x (y + 1) <;>
    simp [h1, h2, h3, h4, h5] <;> simp only [P0, PO] at * <;> omega

theorem odd_to_even (t : ℕ) (h : ∀ x y, state t x y = decide (PO x y)) :
    ∀ x y, state (t + 1) x y = decide (PE x y) := by
  apply step t PO PE h
  intro x y
  by_cases h1 : PO x y <;> by_cases h2 : PO (x - 1) y <;> by_cases h3 : PO (x + 1) y <;>
    by_cases h4 : PO x (y - 1) <;> by_cases h5 : PO x (y + 1) <;>
    simp [h1, h2, h3, h4, h5] <;> simp only [PO, PE] at * <;> omega

theorem even_to_odd (t : ℕ) (h : ∀ x y, state t x y = decide (PE x y)) :
    ∀ x y, state (t + 1) x y = decide (PO x y) := by
  apply step t PE PO h
  intro x y
  by_cases h1 : PE x y <;> by_cases h2 : PE (x - 1) y <;> by_cases h3 : PE (x + 1) y <;>
    by_cases h4 : PE x (y - 1) <;> by_cases h5 : PE x (y + 1) <;>
    simp [h1, h2, h3, h4, h5] <;> simp only [PO, PE] at * <;> omega

theorem state_pattern (m : ℕ) :
    (∀ x y, state (2 * m + 1) x y = decide (PO x y)) ∧
      (∀ x y, state (2 * m + 2) x y = decide (PE x y)) := by
  induction m with
  | zero => exact ⟨stage1, odd_to_even 1 stage1⟩
  | succ m ih =>
    have h1 := even_to_odd (2 * m + 2) ih.2
    exact ⟨h1, odd_to_even (2 * (m + 1) + 1) h1⟩

theorem a_odd (n : ℕ) (h : n % 2 = 1) : a n + 1 = 3 * 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 1 := ⟨n / 2, by omega⟩
  have hs := (state_pattern m).1
  have key : ∀ k, (∑ j ∈ Finset.range (k + 2), if state (2 * m + 1) (j : ℤ) 0 then
      2 ^ (k + 1 - j) else 0) + 1 = 3 * 2 ^ k := by
    intro k
    induction k with
    | zero =>
      simp [Finset.sum_range_succ, hs, PO]
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hk : (∑ j ∈ Finset.range (k + 2), if state (2 * m + 1) (j : ℤ) 0 then
          2 ^ (k + 1 + 1 - j) else 0) = 2 * ∑ j ∈ Finset.range (k + 2),
          if state (2 * m + 1) (j : ℤ) 0 then 2 ^ (k + 1 - j) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        split_ifs
        · rw [show k + 1 + 1 - j = (k + 1 - j) + 1 by omega, pow_succ]; ring
        · simp
      rw [hk, hs]
      have : decide (PO ((k + 1 + 1 : ℕ) : ℤ) 0) = true := by
        simp only [PO, decide_eq_true_eq]; push_cast; omega
      rw [this, if_pos rfl, show k + 1 + 1 - (k + 1 + 1) = 0 by omega, pow_zero, pow_succ]
      omega
  have := key (2 * m)
  unfold a
  rw [show 2 * m + 1 - 1 = 2 * m by omega]
  exact this

theorem a_even (n : ℕ) (h : n % 2 = 0) : a n + 1 = 2 ^ (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · decide
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m + 2 := ⟨n / 2 - 1, by omega⟩
  have hs := (state_pattern m).2
  have hall : ∀ j : ℕ, state (2 * m + 2) (j : ℤ) 0 = true := by
    intro j; rw [hs, decide_eq_true_iff]; unfold PE; omega
  unfold a
  simp only [hall, if_true]
  have := Nat.geomSum_eq (m := 2) (le_refl 2) (2 * m + 3)
  rw [← Finset.sum_range_reflect] at this
  rw [show 2 * m + 2 + 1 = 2 * m + 3 by omega]
  have e : ∑ j ∈ Finset.range (2 * m + 3), 2 ^ (2 * m + 2 - j) =
      ∑ j ∈ Finset.range (2 * m + 3), 2 ^ (2 * m + 3 - 1 - j) := by
    apply Finset.sum_congr rfl; intro j _; congr 1
  rw [e, this]
  have : 2 ^ (2 * m + 3) ≥ 1 := Nat.one_le_two_pow
  omega

/-- Control: the first eight terms. -/
theorem first_terms : (List.range 8).map a = [1, 2, 7, 11, 31, 47, 127, 191] := by
  have e0 := a_even 0 rfl; have e2 := a_even 2 rfl; have e4 := a_even 4 rfl
  have e6 := a_even 6 rfl
  have o1 := a_odd 1 rfl; have o3 := a_odd 3 rfl; have o5 := a_odd 5 rfl
  have o7 := a_odd 7 rfl
  norm_num at e0 e2 e4 e6 o1 o3 o5 o7
  simp [List.range_succ]
  omega

/-- Barker's formula for even `n`: `a(n) = (2^(n+3) - 4)/4`, i.e. `4 a(n) = 2^(n+3) - 4`. -/
theorem formula_even (n : ℕ) (h : n % 2 = 0) : 4 * (a n : ℤ) = 2 ^ (n + 3) - 4 := by
  have := a_even n h
  have e : (a n : ℤ) + 1 = 2 ^ (n + 1) := by exact_mod_cast this
  rw [pow_add 2 (n + 1) 2] at *
  linear_combination 4 * e

/-- Barker's formula for odd `n`: `a(n) = (3*2^(n+1) - 4)/4`, i.e. `4 a(n) = 3·2^(n+1) - 4`. -/
theorem formula_odd (n : ℕ) (h : n % 2 = 1) : 4 * (a n : ℤ) = 3 * 2 ^ (n + 1) - 4 := by
  have := a_odd n h
  have e : (a n : ℤ) + 1 = 3 * 2 ^ (n - 1) := by exact_mod_cast this
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega] at e
  rw [show m + 1 + 1 = m + 2 by omega, pow_add]
  linear_combination 4 * e

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have c3 := formula_odd (k + 3) (by omega)
    have c2 := formula_even (k + 2) (by omega)
    have c1 := formula_odd (k + 1) (by omega)
    have c0 := formula_even k hk
    simp only [pow_add] at c3 c2 c1 c0
    have h : 4 * ((a (k + 3) : ℤ) - (a (k + 2) + 4 * a (k + 1) - 4 * a k)) = 0 := by
      linear_combination c3 - c2 - 4 * c1 + 4 * c0
    have := (mul_eq_zero.mp h).resolve_left (by norm_num)
    linarith
  · have c3 := formula_even (k + 3) (by omega)
    have c2 := formula_odd (k + 2) (by omega)
    have c1 := formula_even (k + 1) (by omega)
    have c0 := formula_odd k hk
    simp only [pow_add] at c3 c2 c1 c0
    have h : 4 * ((a (k + 3) : ℤ) - (a (k + 2) + 4 * a (k + 1) - 4 * a k)) = 0 := by
      linear_combination c3 - c2 - 4 * c1 + 4 * c0
    have := (mul_eq_zero.mp h).resolve_left (by norm_num)
    linarith

/-- Barker's g.f. with the denominator cleared: `A(x) (1-x)(1-2x)(1+2x) = 1 + x + x^2`. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X) * (1 + 2 * X)) =
    (1 + X + X ^ 2 : PowerSeries ℤ) := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have h4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
  have hD : A * ((1 - X) * (1 - 2 * X) * (1 + 2 * X)) =
      A - A * X ^ 1 - C 4 * (A * X ^ 2) + C 4 * (A * X ^ 3) := by rw [h4]; ring
  have hN : (1 + X + X ^ 2 : PowerSeries ℤ) = 1 + X ^ 1 + X ^ 2 := by ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_one,
    coeff_X_pow]
  have v0 : a 0 = 1 := by have := a_even 0 rfl; norm_num at this; omega
  have v1 : a 1 = 2 := by have := a_odd 1 rfl; norm_num at this; omega
  have v2 : a 2 = 7 := by have := a_even 2 rfl; norm_num at this; omega
  rcases Nat.lt_or_ge n 3 with h | h
  · interval_cases n
    · simp only [v0]; norm_num
    · simp only [v0, v1]; norm_num
    · simp only [v0, v1, v2]; norm_num
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, if_false]
    linear_combination r

end OMA.S_oeis_a284354

theorem OMA.solution : type_of% @OMA.S_oeis_a284354.main :=
  ⟨OMA.S_oeis_a284354.gf, OMA.S_oeis_a284354.formula_even, OMA.S_oeis_a284354.formula_odd,
    OMA.S_oeis_a284354.recurrence⟩
