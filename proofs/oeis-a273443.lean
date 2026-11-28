import OMAStatements.S_oeis_a273443

namespace OMA.S_oeis_a273443

open PowerSeries



theorem testBit721 (k : ℕ) :
    Nat.testBit 721 k = decide (k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 9) := by
  rcases Nat.lt_or_ge k 10 with h | h
  · interval_cases k <;> decide
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num : 721 < 2 ^ 10)
      (Nat.pow_le_pow_right (by norm_num) h))]
    simp; omega

/-- The general step, for stages described by predicates. -/
theorem step (t : ℕ) (P Q : ℤ → ℤ → Prop) [∀ x y, Decidable (P x y)] [∀ x y, Decidable (Q x y)]
    (hP : ∀ x y, state t x y = decide (P x y))
    (hQ : ∀ x y, (Q x y ↔ (let k := (if P x y then 1 else 0) + 2 * ((if P (x - 1) y then 1 else 0)
      + (if P (x + 1) y then 1 else 0) + (if P x (y - 1) then 1 else 0)
      + (if P x (y + 1) then 1 else 0)); k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 9))) :
    ∀ x y, state (t + 1) x y = decide (Q x y) := by
  intro x y
  show Nat.testBit 721 _ = _
  rw [testBit721, hP, hP, hP, hP, hP]
  apply Bool.decide_congr
  rw [hQ]
  simp only [Bool.toNat, decide_eq_true_eq, cond_eq_if]

def P0 (x y : ℤ) : Prop := x = 0 ∧ y = 0
def P1 (x y : ℤ) : Prop := ¬ ((x = 0 ∧ (y = 0 ∨ y = 1 ∨ y = -1)) ∨ (y = 0 ∧ (x = 1 ∨ x = -1)))
def P2 (x y : ℤ) : Prop := ¬ ((x = 1 ∨ x = -1) ∧ (y = 1 ∨ y = -1))
def P3 (x y : ℤ) : Prop := ¬ (-1 ≤ x ∧ x ≤ 1 ∧ -1 ≤ y ∧ y ≤ 1 ∧ ¬ (x = 0 ∧ y = 0))
def P4 (x y : ℤ) : Prop := ¬ (x = 0 ∧ y = 0)

instance (x y : ℤ) : Decidable (P0 x y) := by unfold P0; infer_instance
instance (x y : ℤ) : Decidable (P1 x y) := by unfold P1; infer_instance
instance (x y : ℤ) : Decidable (P2 x y) := by unfold P2; infer_instance
instance (x y : ℤ) : Decidable (P3 x y) := by unfold P3; infer_instance
instance (x y : ℤ) : Decidable (P4 x y) := by unfold P4; infer_instance

theorem stage1 : ∀ x y, state 1 x y = decide (P1 x y) := by
  apply step 0 P0 P1 (fun x y => rfl)
  intro x y
  by_cases h1 : P0 x y <;> by_cases h2 : P0 (x - 1) y <;> by_cases h3 : P0 (x + 1) y <;>
    by_cases h4 : P0 x (y - 1) <;> by_cases h5 : P0 x (y + 1) <;>
    simp [h1, h2, h3, h4, h5] <;> simp only [P0, P1] at * <;> omega

theorem stage2 : ∀ x y, state 2 x y = decide (P2 x y) := by
  apply step 1 P1 P2 stage1
  intro x y
  by_cases h1 : P1 x y <;> by_cases h2 : P1 (x - 1) y <;> by_cases h3 : P1 (x + 1) y <;>
    by_cases h4 : P1 x (y - 1) <;> by_cases h5 : P1 x (y + 1) <;>
    simp [h1, h2, h3, h4, h5] <;> simp only [P1, P2] at * <;> omega

theorem stage3 : ∀ x y, state 3 x y = decide (P3 x y) := by
  apply step 2 P2 P3 stage2
  intro x y
  by_cases h1 : P2 x y <;> by_cases h2 : P2 (x - 1) y <;> by_cases h3 : P2 (x + 1) y <;>
    by_cases h4 : P2 x (y - 1) <;> by_cases h5 : P2 x (y + 1) <;>
    simp [h1, h2, h3, h4, h5] <;> simp only [P2, P3] at * <;> omega

theorem stage4 : ∀ x y, state 4 x y = decide (P4 x y) := by
  apply step 3 P3 P4 stage3
  intro x y
  by_cases h1 : P3 x y <;> by_cases h2 : P3 (x - 1) y <;> by_cases h3 : P3 (x + 1) y <;>
    by_cases h4 : P3 x (y - 1) <;> by_cases h5 : P3 x (y + 1) <;>
    simp [h1, h2, h3, h4, h5] <;> simp only [P3, P4] at * <;> omega

theorem stage_ge (t : ℕ) (ht : 4 ≤ t) : ∀ x y, state t x y = decide (P4 x y) := by
  induction t, ht using Nat.le_induction with
  | base => exact stage4
  | succ t _ ih =>
    apply step t P4 P4 ih
    intro x y
    by_cases h1 : P4 x y <;> by_cases h2 : P4 (x - 1) y <;> by_cases h3 : P4 (x + 1) y <;>
      by_cases h4 : P4 x (y - 1) <;> by_cases h5 : P4 x (y + 1) <;>
      simp [h1, h2, h3, h4, h5] <;> simp only [P4] at * <;> omega

theorem on_ge (t : ℕ) (ht : 4 ≤ t) : on t = (2 * t + 1) ^ 2 - 1 := by
  unfold on
  have : ((Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter fun p : ℕ × ℕ =>
      state t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t)) =
      (Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).erase (t, t) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_erase, stage_ge t ht, decide_eq_true_iff]
    unfold P4
    constructor
    · rintro ⟨hp, h⟩
      refine ⟨?_, hp⟩
      rintro rfl
      exact h ⟨by simp, by simp⟩
    · rintro ⟨hne, hp⟩
      refine ⟨hp, ?_⟩
      rintro ⟨h1, h2⟩
      apply hne
      ext
      · simp only; omega
      · simp only; omega
  rw [this, Finset.card_erase_of_mem (by simp; omega), Finset.card_product, Finset.card_range]
  ring_nf

theorem on_small : on 0 = 1 ∧ on 1 = 4 ∧ on 2 = 21 ∧ on 3 = 41 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- Control: the first eight terms. -/
theorem first_terms : (List.range 8).map on = [1, 4, 21, 41, 80, 120, 168, 224] := by
  obtain ⟨h0, h1, h2, h3⟩ := on_small
  simp [List.range_succ, h0, h1, h2, h3, on_ge]

/-- Barker's formula `a(n) = 4n(1+n)` for `n > 3`. -/
theorem closed_form (n : ℕ) (hn : 3 < n) : on n = 4 * n * (1 + n) := by
  rw [on_ge n hn]
  have : (2 * n + 1) ^ 2 = 4 * n * (1 + n) + 1 := by ring
  omega

/-- Barker's recurrence. -/
theorem recurrence (n : ℕ) (hn : 6 < n) :
    (on n : ℤ) = 3 * on (n - 1) - 3 * on (n - 2) + on (n - 3) := by
  rw [closed_form n (by omega), closed_form (n - 1) (by omega), closed_form (n - 2) (by omega),
    closed_form (n - 3) (by omega)]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
    show k + 7 - 3 = k + 4 by omega]
  push_cast; ring

/-- Barker's g.f. with the denominator cleared:
`A(x) (1-x)^3 = 1 + x + 12x^2 - 11x^3 + 16x^4 - 18x^5 + 7x^6`. -/
theorem gf : mk (fun n => (on n : ℤ)) * (1 - X) ^ 3 =
    (1 + X + 12 * X ^ 2 - 11 * X ^ 3 + 16 * X ^ 4 - 18 * X ^ 5 + 7 * X ^ 6 : PowerSeries ℤ) := by
  set A : PowerSeries ℤ := mk (fun n => (on n : ℤ)) with hA
  have h3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat C 3
  have h12 : (C (12 : ℤ) : PowerSeries ℤ) = 12 := map_ofNat C 12
  have h11 : (C (11 : ℤ) : PowerSeries ℤ) = 11 := map_ofNat C 11
  have h16 : (C (16 : ℤ) : PowerSeries ℤ) = 16 := map_ofNat C 16
  have h18 : (C (18 : ℤ) : PowerSeries ℤ) = 18 := map_ofNat C 18
  have h7 : (C (7 : ℤ) : PowerSeries ℤ) = 7 := map_ofNat C 7
  have hD : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - A * X ^ 3 := by
    rw [h3]; ring
  have hN : (1 + X + 12 * X ^ 2 - 11 * X ^ 3 + 16 * X ^ 4 - 18 * X ^ 5 + 7 * X ^ 6 :
      PowerSeries ℤ) = 1 + X ^ 1 + C 12 * X ^ 2 - C 11 * X ^ 3 + C 16 * X ^ 4 - C 18 * X ^ 5
        + C 7 * X ^ 6 := by
    rw [h12, h11, h16, h18, h7]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_one,
    coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge n 7 with h | h
  · obtain ⟨h0, h1, h2, h3⟩ := on_small
    have h4 := closed_form 4 (by norm_num)
    have h5 := closed_form 5 (by norm_num)
    have h6 := closed_form 6 (by norm_num)
    norm_num at h4 h5 h6
    interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6]
  · have r := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, if_true,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n - 1 ≠ 0 by omega,
      show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
      show n - 5 ≠ 0 by omega, show n - 6 ≠ 0 by omega, if_false]
    linear_combination r

end OMA.S_oeis_a273443

theorem OMA.solution : type_of% @OMA.S_oeis_a273443.main :=
  ⟨OMA.S_oeis_a273443.closed_form, OMA.S_oeis_a273443.recurrence, OMA.S_oeis_a273443.gf⟩
