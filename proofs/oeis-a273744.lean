import OMAStatements.S_oeis_a273744

namespace OMA.S_oeis_a273744

open PowerSeries




theorem testBit901 (k : ℕ) :
    Nat.testBit 901 k = decide (k = 0 ∨ k = 2 ∨ k = 7 ∨ k = 8 ∨ k = 9) := by
  rcases Nat.lt_or_ge k 10 with h | h
  · interval_cases k <;> decide
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num : 901 < 2 ^ 10)
      (Nat.pow_le_pow_right (by norm_num) h))]
    simp; omega

theorem step (t : ℕ) (P Q : ℤ → ℤ → Prop) [∀ x y, Decidable (P x y)] [∀ x y, Decidable (Q x y)]
    (hP : ∀ x y, state t x y = decide (P x y))
    (hQ : ∀ x y, (Q x y ↔ (let k := (if P x y then 1 else 0) + 2 * ((if P (x - 1) y then 1 else 0)
      + (if P (x + 1) y then 1 else 0) + (if P x (y - 1) then 1 else 0)
      + (if P x (y + 1) then 1 else 0)); k = 0 ∨ k = 2 ∨ k = 7 ∨ k = 8 ∨ k = 9))) :
    ∀ x y, state (t + 1) x y = decide (Q x y) := by
  intro x y
  show Nat.testBit 901 _ = _
  rw [testBit901, hP, hP, hP, hP, hP]
  apply Bool.decide_congr
  rw [hQ]
  simp only [Bool.toNat, decide_eq_true_eq, cond_eq_if]

def P0 (x y : ℤ) : Prop := x = 0 ∧ y = 0
def P1 (x y : ℤ) : Prop := ¬ (x = 0 ∧ y = 0)
def PT (_ _ : ℤ) : Prop := True

instance (x y : ℤ) : Decidable (P0 x y) := by unfold P0; infer_instance
instance (x y : ℤ) : Decidable (P1 x y) := by unfold P1; infer_instance
instance (x y : ℤ) : Decidable (PT x y) := by unfold PT; infer_instance

theorem stage1 : ∀ x y, state 1 x y = decide (P1 x y) := by
  apply step 0 P0 P1 (fun x y => rfl)
  intro x y
  by_cases h1 : P0 x y <;> by_cases h2 : P0 (x - 1) y <;> by_cases h3 : P0 (x + 1) y <;>
    by_cases h4 : P0 x (y - 1) <;> by_cases h5 : P0 x (y + 1) <;>
    simp [h1, h2, h3, h4, h5] <;> simp only [P0, P1] at * <;> omega

theorem stage2 : ∀ x y, state 2 x y = decide (PT x y) := by
  apply step 1 P1 PT stage1
  intro x y
  by_cases h1 : P1 x y <;> by_cases h2 : P1 (x - 1) y <;> by_cases h3 : P1 (x + 1) y <;>
    by_cases h4 : P1 x (y - 1) <;> by_cases h5 : P1 x (y + 1) <;>
    simp [h1, h2, h3, h4, h5, PT] <;> simp only [P1] at * <;> omega

theorem stage_ge (t : ℕ) (ht : 2 ≤ t) : ∀ x y, state t x y = true := by
  induction t, ht using Nat.le_induction with
  | base => intro x y; rw [stage2]; rfl
  | succ t _ ih =>
    intro x y
    show Nat.testBit 901 _ = _
    rw [ih, ih, ih, ih, ih]
    decide

theorem on_ge (t : ℕ) (ht : 2 ≤ t) : on t = (2 * t + 1) ^ 2 := by
  unfold on
  rw [Finset.filter_true_of_mem (fun p _ => stage_ge t ht _ _), Finset.card_product,
    Finset.card_range]
  ring

theorem on_small : on 0 = 1 ∧ on 1 = 8 := ⟨by decide +kernel, by decide +kernel⟩

/-- Barker's formula `3 a(n) = n (11 + 12 n + 4 n^2)` for `n > 0`. -/
theorem closed_form (n : ℕ) (hn : 0 < n) : 3 * a n = n * (11 + 12 * n + 4 * n ^ 2) := by
  induction n, hn using Nat.le_induction with
  | base => simp [a, Finset.sum_range_succ, on_small.1, on_small.2]
  | succ n hn ih =>
    have hs : a (n + 1) = a n + on (n + 1) := Finset.sum_range_succ _ _
    rw [hs, on_ge (n + 1) (by omega), mul_add, ih]
    ring

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
  have c5 := closed_form (k + 5) (by omega)
  have c4 := closed_form (k + 4) (by omega)
  have c3 := closed_form (k + 3) (by omega)
  have c2 := closed_form (k + 2) (by omega)
  have c1 := closed_form (k + 1) (by omega)
  have e5 : (3 : ℤ) * a (k + 5) = (k + 5) * (11 + 12 * (k + 5) + 4 * (k + 5) ^ 2) := by
    exact_mod_cast c5
  have e4 : (3 : ℤ) * a (k + 4) = (k + 4) * (11 + 12 * (k + 4) + 4 * (k + 4) ^ 2) := by
    exact_mod_cast c4
  have e3 : (3 : ℤ) * a (k + 3) = (k + 3) * (11 + 12 * (k + 3) + 4 * (k + 3) ^ 2) := by
    exact_mod_cast c3
  have e2 : (3 : ℤ) * a (k + 2) = (k + 2) * (11 + 12 * (k + 2) + 4 * (k + 2) ^ 2) := by
    exact_mod_cast c2
  have e1 : (3 : ℤ) * a (k + 1) = (k + 1) * (11 + 12 * (k + 1) + 4 * (k + 1) ^ 2) := by
    exact_mod_cast c1
  have h : 3 * ((a (k + 5) : ℤ) - (4 * a (k + 4) - 6 * a (k + 3) + 4 * a (k + 2) - a (k + 1)))
      = 0 := by
    linear_combination e5 - 4 * e4 + 6 * e3 - 4 * e2 + e1
  have := (mul_eq_zero.mp h).resolve_left (by norm_num)
  linarith

/-- Barker's g.f. with the denominator cleared: `A(x) (1-x)^4 = 1 + 5x + 4x^2 - 3x^3 + x^4`. -/
theorem gf : mk (fun n => (a n : ℤ)) * (1 - X) ^ 4 =
    (1 + 5 * X + 4 * X ^ 2 - 3 * X ^ 3 + X ^ 4 : PowerSeries ℤ) := by
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have h4 : (C (4 : ℤ) : PowerSeries ℤ) = 4 := map_ofNat C 4
  have h6 : (C (6 : ℤ) : PowerSeries ℤ) = 6 := map_ofNat C 6
  have h5 : (C (5 : ℤ) : PowerSeries ℤ) = 5 := map_ofNat C 5
  have h3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
  have hD : A * (1 - X) ^ 4 =
      A - C 4 * (A * X ^ 1) + C 6 * (A * X ^ 2) - C 4 * (A * X ^ 3) + A * X ^ 4 := by
    rw [h4, h6]; ring
  have hN : (1 + 5 * X + 4 * X ^ 2 - 3 * X ^ 3 + X ^ 4 : PowerSeries ℤ) =
      1 + C 5 * X ^ 1 + C 4 * X ^ 2 - C 3 * X ^ 3 + X ^ 4 := by
    rw [h5, h4, h3]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_one,
    coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge n 5 with h | h
  · have v0 : a 0 = 1 := by simp [a, on_small.1]
    have v1 : a 1 = 9 := by simp [a, Finset.sum_range_succ, on_small.1, on_small.2]
    have v2 : a 2 = 34 := by
      have := closed_form 2 (by norm_num); norm_num at this; omega
    have v3 : a 3 = 83 := by
      have := closed_form 3 (by norm_num); norm_num at this; omega
    have v4 : a 4 = 164 := by
      have := closed_form 4 (by norm_num); norm_num at this; omega
    interval_cases n
    · simp only [v0]; norm_num
    · simp only [v0, v1]; norm_num
    · simp only [v0, v1, v2]; norm_num
    · simp only [v0, v1, v2, v3]; norm_num
    · simp only [v0, v1, v2, v3, v4]; norm_num
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, if_true, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n - 1 ≠ 0 by omega,
      show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, if_false]
    linear_combination r

end OMA.S_oeis_a273744

theorem OMA.solution : type_of% @OMA.S_oeis_a273744.main :=
  ⟨OMA.S_oeis_a273744.closed_form, OMA.S_oeis_a273744.recurrence, OMA.S_oeis_a273744.gf⟩
