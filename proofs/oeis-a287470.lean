import OMAStatements.S_oeis_a287470

namespace OMA.S_oeis_a287470

open PowerSeries



theorem testBit276 (k : ℕ) : Nat.testBit 276 k = decide (k = 2 ∨ k = 4 ∨ k = 8) := by
  rcases Nat.lt_or_ge k 10 with h | h
  · interval_cases k <;> decide
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num : 276 < 2 ^ 10)
      (Nat.pow_le_pow_right (by norm_num) h))]
    simp; omega

/-- The checkerboard diamond of stage t. -/
def D (t : ℕ) (x y : ℤ) : Prop :=
  x + y ≤ t ∧ x - y ≤ t ∧ -x + y ≤ t ∧ -x - y ≤ t ∧ (x + y + t) % 2 = 0

instance (t : ℕ) (x y : ℤ) : Decidable (D t x y) := by unfold D; infer_instance

theorem state_pattern (t : ℕ) : ∀ x y, state t x y = decide (D t x y) := by
  induction t with
  | zero => intro x y; apply Bool.decide_congr; unfold D; push_cast; omega
  | succ t ih =>
    intro x y
    show Nat.testBit 276 _ = _
    rw [testBit276, ih, ih, ih, ih, ih]
    apply Bool.decide_congr
    simp only [Bool.toNat, decide_eq_true_eq, cond_eq_if]
    by_cases h1 : D t x y <;> by_cases h2 : D t (x - 1) y <;> by_cases h3 : D t (x + 1) y <;>
      by_cases h4 : D t x (y - 1) <;> by_cases h5 : D t x (y + 1) <;>
      simp [h1, h2, h3, h4, h5] <;> simp only [D] at * <;> push_cast at * <;> omega

theorem diag (n k : ℕ) : state n (k : ℤ) (k : ℤ) = decide (n % 2 = 0 ∧ 2 * k ≤ n) := by
  rw [state_pattern]
  apply Bool.decide_congr
  unfold D
  omega

/-- Barker's a(n) = 0 for odd n. -/
theorem a_odd (n : ℕ) (h : n % 2 = 1) : a n = 0 := by
  unfold a
  apply Finset.sum_eq_zero
  intro k _
  rw [diag]
  simp; omega

theorem geom2 (m : ℕ) : (∑ i ∈ Finset.range m, 2 ^ i) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- a(2s) + 2^s = 2^(2s+1). -/
theorem a_even_nat (s : ℕ) : a (2 * s) + 2 ^ s = 2 ^ (2 * s + 1) := by
  have hsplit : a (2 * s) = ∑ k ∈ Finset.range (s + 1), 2 ^ s * 2 ^ (s + 1 - 1 - k) := by
    unfold a
    rw [show 2 * s + 1 = (s + 1) + s by omega, Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range s, (if state (2 * s) (((s + 1 + x : ℕ)) : ℤ)
        (((s + 1 + x : ℕ)) : ℤ) then 2 ^ (2 * s - (s + 1 + x)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [diag]; simp; omega
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [diag, if_pos (by simp; omega), ← pow_add]
    congr 1
    omega
  rw [hsplit, ← Finset.mul_sum, Finset.sum_range_reflect (fun i => 2 ^ i) (s + 1)]
  have g := geom2 (s + 1)
  calc 2 ^ s * (∑ j ∈ Finset.range (s + 1), 2 ^ j) + 2 ^ s
      = 2 ^ s * ((∑ j ∈ Finset.range (s + 1), 2 ^ j) + 1) := by ring
    _ = 2 ^ s * 2 ^ (s + 1) := by rw [g]
    _ = 2 ^ (2 * s + 1) := by rw [← pow_add]; congr 1; ring

/-- Barker's closed form for even n. -/
theorem a_even (n : ℕ) (h : n % 2 = 0) : (a n : ℤ) = 2 ^ (n + 1) - 2 ^ (n / 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, n = 2 * s := ⟨n / 2, by omega⟩
  have e := a_even_nat s
  have e' : ((a (2 * s) + 2 ^ s : ℕ) : ℤ) = ((2 ^ (2 * s + 1) : ℕ) : ℤ) := by rw [e]
  push_cast at e'
  rw [show 2 * s / 2 = s by omega]
  linarith

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 6 * a (n - 2) - 8 * a (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 2 = k + 2 by omega, show k + 4 - 4 = k by omega]
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have c4 := a_even (k + 4) (by omega)
    have c2 := a_even (k + 2) (by omega)
    have c0 := a_even k hk
    rw [show (k + 4) / 2 = k / 2 + 2 by omega] at c4
    rw [show (k + 2) / 2 = k / 2 + 1 by omega] at c2
    rw [c4, c2, c0]
    simp only [pow_add, pow_succ]
    ring
  · rw [a_odd (k + 4) (by omega), a_odd (k + 2) (by omega), a_odd k hk]
    norm_num

/-- Barker's g.f. with the denominator cleared: A(x) (1 - 2x)(1 + 2x)(1 - 2x^2) = 1. -/
theorem gf : mk (fun n => (a n : ℤ)) * ((1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2)) =
    (1 : PowerSeries ℤ) := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have h6 : (C (6 : ℤ) : PowerSeries ℤ) = 6 := map_ofNat C 6
  have h8 : (C (8 : ℤ) : PowerSeries ℤ) = 8 := map_ofNat C 8
  have hD : A * ((1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2)) =
      A - C 6 * (A * X ^ 2) + C 8 * (A * X ^ 4) := by rw [h6, h8]; ring
  rw [hD]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_one]
  have v0 : (a 0 : ℤ) = 1 := by rw [a_even 0 rfl]; norm_num
  have v2 : (a 2 : ℤ) = 6 := by rw [a_even 2 rfl]; norm_num
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n
    · simp only [v0]; norm_num
    · simp only [a_odd 1 rfl]; norm_num
    · simp only [v0, v2]; norm_num
    · simp only [a_odd 1 rfl, a_odd 3 rfl]; norm_num
  · have r := recurrence n (by omega)
    simp only [show 2 ≤ n by omega, show 4 ≤ n by omega, if_true, show n ≠ 0 by omega,
      if_false]
    linear_combination r

/-- Barker's four conjectures. -/
theorem conjecture :
    mk (fun n => (a n : ℤ)) * ((1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2)) =
      (1 : PowerSeries ℤ) ∧
    (∀ n : ℕ, n % 2 = 0 → (a n : ℤ) = 2 ^ (n + 1) - 2 ^ (n / 2)) ∧
    (∀ n : ℕ, n % 2 = 1 → a n = 0) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 6 * a (n - 2) - 8 * a (n - 4)) :=
  ⟨gf, a_even, a_odd, recurrence⟩

end OMA.S_oeis_a287470

theorem OMA.solution : type_of% @OMA.S_oeis_a287470.main :=
  OMA.S_oeis_a287470.conjecture
