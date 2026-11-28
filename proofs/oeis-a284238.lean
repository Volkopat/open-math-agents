import OMAStatements.S_oeis_a284238

namespace OMA.S_oeis_a284238

open PowerSeries



theorem testBit833 (k : ℕ) : Nat.testBit 833 k = decide (k = 0 ∨ k = 6 ∨ k = 8 ∨ k = 9) := by
  rcases Nat.lt_or_ge k 10 with h | h
  · interval_cases k <;> decide
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num : 833 < 2 ^ 10)
      (Nat.pow_le_pow_right (by norm_num) h))]
    simp; omega

/-- Number of ON neighbors. -/
def nb (P : ℤ → ℤ → Prop) [∀ x y, Decidable (P x y)] (x y : ℤ) : ℕ :=
  (if P (x - 1) y then 1 else 0) + (if P (x + 1) y then 1 else 0) +
    (if P x (y - 1) then 1 else 0) + (if P x (y + 1) then 1 else 0)

/-- Rule 833 in terms of an ON predicate `P` for stage `t`. -/
theorem step (t : ℕ) (P Q : ℤ → ℤ → Prop) [∀ x y, Decidable (P x y)] [∀ x y, Decidable (Q x y)]
    (hP : ∀ x y, state t x y = decide (P x y))
    (hQ : ∀ x y, Q x y ↔ (P x y ∧ nb P x y = 4) ∨
      (¬ P x y ∧ (nb P x y = 0 ∨ nb P x y = 3 ∨ nb P x y = 4))) :
    ∀ x y, state (t + 1) x y = decide (Q x y) := by
  intro x y
  show Nat.testBit 833 _ = _
  rw [testBit833, hP, hP, hP, hP, hP]
  apply Bool.decide_congr
  rw [hQ]
  unfold nb
  by_cases h1 : P x y <;> by_cases h2 : P (x - 1) y <;> by_cases h3 : P (x + 1) y <;>
    by_cases h4 : P x (y - 1) <;> by_cases h5 : P x (y + 1) <;> simp [h1, h2, h3, h4, h5]

def P0 (x y : ℤ) : Prop := x = 0 ∧ y = 0
/-- The OFF cells of stage 1: the diamond of radius 1. -/
def S1 (x y : ℤ) : Prop := x + y ≤ 1 ∧ x - y ≤ 1 ∧ y - x ≤ 1 ∧ -x - y ≤ 1
/-- The checkerboard diamond: `|x| + |y| ≤ t` and `x + y + t` even. -/
def Dm (t : ℕ) (x y : ℤ) : Prop :=
  x + y ≤ t ∧ x - y ≤ t ∧ y - x ≤ t ∧ -x - y ≤ t ∧ (x + y + t) % 2 = 0
/-- The OFF cells of stage 2: `Dm 2` without the origin. -/
def S2 (x y : ℤ) : Prop := Dm 2 x y ∧ ¬ (x = 0 ∧ y = 0)

instance (x y : ℤ) : Decidable (P0 x y) := by unfold P0; infer_instance
instance (x y : ℤ) : Decidable (S1 x y) := by unfold S1; infer_instance
instance (t : ℕ) (x y : ℤ) : Decidable (Dm t x y) := by unfold Dm; infer_instance
instance (x y : ℤ) : Decidable (S2 x y) := by unfold S2; infer_instance

theorem stage1 : ∀ x y, state 1 x y = decide (¬ S1 x y) := by
  apply step 0 P0 (fun x y => ¬ S1 x y) (fun x y => rfl)
  intro x y
  rcases (show (x + y ≥ 3 ∨ x - y ≥ 3 ∨ y - x ≥ 3 ∨ -x - y ≥ 3) ∨
      ((-2 ≤ x ∧ x ≤ 2) ∧ (-2 ≤ y ∧ y ≤ 2)) by omega) with hfar | ⟨⟨hx1, hx2⟩, hy1, hy2⟩
  · have c : ¬ P0 x y := by unfold P0; omega
    have n1 : ¬ P0 (x - 1) y := by unfold P0; omega
    have n2 : ¬ P0 (x + 1) y := by unfold P0; omega
    have n3 : ¬ P0 x (y - 1) := by unfold P0; omega
    have n4 : ¬ P0 x (y + 1) := by unfold P0; omega
    have q : ¬ S1 x y := by unfold S1; omega
    unfold nb
    simp [c, n1, n2, n3, n4, q]
  · interval_cases x <;> interval_cases y <;> decide

theorem stage2 : ∀ x y, state 2 x y = decide (¬ S2 x y) := by
  apply step 1 (fun x y => ¬ S1 x y) (fun x y => ¬ S2 x y) stage1
  intro x y
  rcases (show (x + y ≥ 4 ∨ x - y ≥ 4 ∨ y - x ≥ 4 ∨ -x - y ≥ 4) ∨
      ((-3 ≤ x ∧ x ≤ 3) ∧ (-3 ≤ y ∧ y ≤ 3)) by omega) with hfar | ⟨⟨hx1, hx2⟩, hy1, hy2⟩
  · have c : ¬ S1 x y := by unfold S1; omega
    have n1 : ¬ S1 (x - 1) y := by unfold S1; omega
    have n2 : ¬ S1 (x + 1) y := by unfold S1; omega
    have n3 : ¬ S1 x (y - 1) := by unfold S1; omega
    have n4 : ¬ S1 x (y + 1) := by unfold S1; omega
    have q : ¬ S2 x y := by unfold S2 Dm; push_cast; omega
    unfold nb
    simp [c, n1, n2, n3, n4, q]
  · interval_cases x <;> interval_cases y <;> decide

theorem stage3 : ∀ x y, state 3 x y = decide (¬ Dm 3 x y) := by
  apply step 2 (fun x y => ¬ S2 x y) (fun x y => ¬ Dm 3 x y) stage2
  intro x y
  rcases (show (x + y ≥ 4 ∨ x - y ≥ 4 ∨ y - x ≥ 4 ∨ -x - y ≥ 4) ∨
      ((-3 ≤ x ∧ x ≤ 3) ∧ (-3 ≤ y ∧ y ≤ 3)) by omega) with hfar | ⟨⟨hx1, hx2⟩, hy1, hy2⟩
  · have c : ¬ S2 x y := by unfold S2 Dm; push_cast; omega
    have n1 : ¬ S2 (x - 1) y := by unfold S2 Dm; push_cast; omega
    have n2 : ¬ S2 (x + 1) y := by unfold S2 Dm; push_cast; omega
    have n3 : ¬ S2 x (y - 1) := by unfold S2 Dm; push_cast; omega
    have n4 : ¬ S2 x (y + 1) := by unfold S2 Dm; push_cast; omega
    have q : ¬ Dm 3 x y := by unfold Dm; push_cast; omega
    unfold nb
    simp [c, n1, n2, n3, n4, q]
  · interval_cases x <;> interval_cases y <;> decide

/-- A cell of odd parity has a neighbor in `Dm t` iff it lies in `Dm (t + 1)`. -/
theorem key (t : ℕ) (x y : ℤ) (hp : (x + y + t) % 2 = 1) :
    (Dm t (x - 1) y ∨ Dm t (x + 1) y ∨ Dm t x (y - 1) ∨ Dm t x (y + 1)) ↔ Dm (t + 1) x y := by
  unfold Dm
  push_cast
  constructor
  · rintro (h | h | h | h) <;> omega
  · intro h
    rcases (show 0 < x ∨ x < 0 ∨ (x = 0 ∧ 0 < y) ∨ (x = 0 ∧ y < 0) ∨ (x = 0 ∧ y = 0) by omega)
      with hx | hx | hx | hx | hx
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
    · left; omega

theorem trans (t : ℕ) (h : ∀ x y, state t x y = decide (¬ Dm t x y)) :
    ∀ x y, state (t + 1) x y = decide (¬ Dm (t + 1) x y) := by
  apply step t (fun x y => ¬ Dm t x y) (fun x y => ¬ Dm (t + 1) x y) h
  intro x y
  rcases Int.emod_two_eq_zero_or_one (x + y + t) with hp | hp
  · have n1 : ¬ Dm t (x - 1) y := by unfold Dm; omega
    have n2 : ¬ Dm t (x + 1) y := by unfold Dm; omega
    have n3 : ¬ Dm t x (y - 1) := by unfold Dm; omega
    have n4 : ¬ Dm t x (y + 1) := by unfold Dm; omega
    have q : ¬ Dm (t + 1) x y := by unfold Dm; push_cast; omega
    unfold nb
    by_cases hc : Dm t x y <;> simp [n1, n2, n3, n4, q, hc]
  · have hc : ¬ Dm t x y := by unfold Dm; omega
    have hk := key t x y hp
    unfold nb
    by_cases h1 : Dm t (x - 1) y <;> by_cases h2 : Dm t (x + 1) y <;>
      by_cases h3 : Dm t x (y - 1) <;> by_cases h4 : Dm t x (y + 1) <;>
      simp [h1, h2, h3, h4, hc, ← hk]

theorem pattern (r : ℕ) : ∀ x y, state (r + 3) x y = decide (¬ Dm (r + 3) x y) := by
  induction r with
  | zero => exact stage3
  | succ r ih => exact trans (r + 3) ih

/-- On the axis, from stage 3 on: the cell `(j, 0)`, `j ≤ n`, is ON iff `j + n` is odd. -/
theorem axis (n j : ℕ) (hn : 3 ≤ n) (hj : j ≤ n) : state n (j : ℤ) 0 = decide ((j + n) % 2 = 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 3 := ⟨n - 3, by omega⟩
  rw [pattern r]
  apply Bool.decide_congr
  unfold Dm
  push_cast
  omega

theorem a_zero : a 0 = 1 := by decide
theorem a_one : a 1 = 0 := by
  unfold a
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, stage1, stage1]
  decide
theorem a_two : a 2 = 6 := by
  unfold a
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    stage2, stage2, stage2]
  decide

/-- From stage 3 on, `a(n)` is the sum of `2^i` over the odd `i ≤ n`. -/
theorem a_odd_powers (n : ℕ) (hn : 3 ≤ n) :
    a n = ∑ i ∈ Finset.range (n + 1), if i % 2 = 1 then 2 ^ i else 0 := by
  have hr := Finset.sum_range_reflect (fun j => if state n (j : ℤ) 0 then 2 ^ (n - j) else 0)
    (n + 1)
  unfold a
  rw [← hr]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [axis n (n + 1 - 1 - i) hn (by omega)]
  have e : n - (n + 1 - 1 - i) = i := by omega
  rw [e]
  by_cases h : i % 2 = 1
  · rw [if_pos h, if_pos (show decide ((n + 1 - 1 - i + n) % 2 = 1) = true by simp; omega)]
  · rw [if_neg h, if_neg (show ¬ decide ((n + 1 - 1 - i + n) % 2 = 1) = true by simp; omega)]

/-- `3 * Sum_{i odd, i < 2m} 2^i + 2 = 2 * 4^m`. -/
theorem odd_sum (m : ℕ) :
    3 * (∑ i ∈ Finset.range (2 * m), if i % 2 = 1 then 2 ^ i else 0) + 2 = 2 * 4 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      if_neg (show ¬ (2 * m % 2 = 1) by omega), if_pos (show (2 * m + 1) % 2 = 1 by omega),
      pow_succ 4 m, pow_succ, pow_mul]
    norm_num
    omega

theorem odd_sum_even (m : ℕ) :
    3 * (∑ i ∈ Finset.range (2 * m + 1), if i % 2 = 1 then 2 ^ i else 0) + 2 = 2 * 4 ^ m := by
  rw [Finset.sum_range_succ, if_neg (show ¬ (2 * m % 2 = 1) by omega), add_zero]
  exact odd_sum m

theorem odd_sum_odd (m : ℕ) :
    3 * (∑ i ∈ Finset.range (2 * m + 1 + 1), if i % 2 = 1 then 2 ^ i else 0) + 2 = 8 * 4 ^ m := by
  rw [Finset.sum_range_succ, if_pos (show (2 * m + 1) % 2 = 1 by omega)]
  have h := odd_sum_even m
  rw [pow_succ, pow_mul]
  norm_num
  omega

theorem a_even_z (m : ℕ) (hm : 2 ≤ m) : 3 * (a (2 * m) : ℤ) = 2 * 4 ^ m - 2 := by
  rw [a_odd_powers (2 * m) (by omega)]
  have h := odd_sum_even m
  have h' : ((3 * (∑ i ∈ Finset.range (2 * m + 1), if i % 2 = 1 then 2 ^ i else 0) + 2 : ℕ) :
      ℤ) = ((2 * 4 ^ m : ℕ) : ℤ) := by rw [h]
  push_cast at h' ⊢
  linarith

theorem a_odd_z (m : ℕ) (hm : 1 ≤ m) : 3 * (a (2 * m + 1) : ℤ) = 8 * 4 ^ m - 2 := by
  rw [a_odd_powers (2 * m + 1) (by omega)]
  have h := odd_sum_odd m
  have h' : ((3 * (∑ i ∈ Finset.range (2 * m + 1 + 1), if i % 2 = 1 then 2 ^ i else 0) + 2 :
      ℕ) : ℤ) = ((8 * 4 ^ m : ℕ) : ℤ) := by rw [h]
  push_cast at h' ⊢
  linarith

/-- Chai Wah Wu's recurrence. -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨s, rfl⟩ : ∃ s, m = s + 3 := ⟨m - 3, by omega⟩
    have e0 := a_even_z (s + 3) (by omega)
    have e1 := a_odd_z (s + 2) (by omega)
    have e2 := a_even_z (s + 2) (by omega)
    have e3 := a_odd_z (s + 1) (by omega)
    rw [hm, show s + 3 + (s + 3) - 1 = 2 * (s + 2) + 1 by omega,
      show s + 3 + (s + 3) - 2 = 2 * (s + 2) by omega,
      show s + 3 + (s + 3) - 3 = 2 * (s + 1) + 1 by omega,
      show s + 3 + (s + 3) = 2 * (s + 3) by omega]
    simp only [pow_succ] at e0 e1 e2 e3
    linarith
  · obtain ⟨s, rfl⟩ : ∃ s, m = s + 3 := ⟨m - 3, by omega⟩
    have e0 := a_odd_z (s + 3) (by omega)
    have e1 := a_even_z (s + 3) (by omega)
    have e2 := a_odd_z (s + 2) (by omega)
    have e3 := a_even_z (s + 2) (by omega)
    rw [hm, show 2 * (s + 3) + 1 - 1 = 2 * (s + 3) by omega,
      show 2 * (s + 3) + 1 - 2 = 2 * (s + 2) + 1 by omega,
      show 2 * (s + 3) + 1 - 3 = 2 * (s + 2) by omega]
    simp only [pow_succ] at e0 e1 e2 e3
    linarith

theorem a_values : a 3 = 10 ∧ a 4 = 10 ∧ a 5 = 42 := by
  have h3 := a_odd_z 1 le_rfl
  have h4 := a_even_z 2 le_rfl
  have h5 := a_odd_z 2 (by norm_num)
  norm_num at h3 h4 h5
  omega

/-- Wu's g.f. with the denominator multiplied out. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((X - 1) * (2 * X - 1) * (2 * X + 1)) =
    (16 * X ^ 5 - 24 * X ^ 4 + 8 * X ^ 3 + 2 * X ^ 2 - X + 1 : PowerSeries ℤ) := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have h4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
  have h16 : (C (16 : ℤ) : PowerSeries ℤ) = 16 := map_ofNat C 16
  have h24 : (C (24 : ℤ) : PowerSeries ℤ) = 24 := map_ofNat C 24
  have h8 : (C (8 : ℤ) : PowerSeries ℤ) = 8 := map_ofNat C 8
  have h2 : (C (2 : ℤ) : PowerSeries ℤ) = 2 := map_ofNat C 2
  have hD : A * ((X - 1) * (2 * X - 1) * (2 * X + 1)) =
      C 4 * (A * X ^ 3) - C 4 * (A * X ^ 2) - A * X ^ 1 + A := by
    rw [h4]; ring
  have hN : (16 * X ^ 5 - 24 * X ^ 4 + 8 * X ^ 3 + 2 * X ^ 2 - X + 1 : PowerSeries ℤ) =
      C 16 * X ^ 5 - C 24 * X ^ 4 + C 8 * X ^ 3 + C 2 * X ^ 2 - X ^ 1 + 1 := by
    rw [h16, h24, h8, h2]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_one,
    coeff_X_pow, coeff_C]
  obtain ⟨v3, v4, v5⟩ := a_values
  rcases Nat.lt_or_ge n 6 with h | h
  · interval_cases n <;> norm_num [a_zero, a_one, a_two, v3, v4, v5]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, if_true, show n ≠ 0 by omega,
      show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      show n ≠ 5 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega, if_false]
    linear_combination r

/-- Wu's two conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = a (n - 1) + 4 * a (n - 2) - 4 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((X - 1) * (2 * X - 1) * (2 * X + 1)) =
      (16 * X ^ 5 - 24 * X ^ 4 + 8 * X ^ 3 + 2 * X ^ 2 - X + 1 : PowerSeries ℤ) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a284238

theorem OMA.solution : type_of% @OMA.S_oeis_a284238.main :=
  OMA.S_oeis_a284238.conjecture
