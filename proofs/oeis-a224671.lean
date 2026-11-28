import OMAStatements.S_oeis_a224671
import Mathlib

/-!
The argument follows the accepted proof of the template entry OEIS A224669: a per-row linear
recurrence is checked by the kernel at its first index and propagated through the defining
sum, then summed over the first row. Here the recurrence has characteristic polynomial
`(x-1)^3 (x^2-x-1)` and holds per row from index 2 on. The closed form is a quadratic
polynomial plus a Fibonacci-type sequence `G` with `G 0 = 29`, `G 1 = 24`.
-/

open PowerSeries

namespace IdempotentRows4

open OMA.S_oeis_a224671

set_option maxRecDepth 100000 in
private theorem completion_base : ∀ r : Row,
    completions 7 r + 5 * completions 5 r + completions 2 r =
      4 * completions 6 r + completions 4 r + 2 * completions 3 r := by
  decide +kernel

private theorem completion_rec (k : ℕ) (r : Row) :
    completions (k+7) r + 5 * completions (k+5) r + completions (k+2) r =
      4 * completions (k+6) r + completions (k+4) r + 2 * completions (k+3) r := by
  induction k generalizing r with
  | zero => exact completion_base r
  | succ k ih =>
    have advance (n : ℕ) : completions (n+1) r =
        ∑ s : Row, if compatible r s then completions n s else 0 := rfl
    rw [show k+1+7=k+7+1 by omega, show k+1+5=k+5+1 by omega, show k+1+2=k+2+1 by omega,
      show k+1+6=k+6+1 by omega, show k+1+4=k+4+1 by omega, show k+1+3=k+3+1 by omega,
      advance (k+7), advance (k+5), advance (k+2), advance (k+6), advance (k+4), advance (k+3)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp [ih]

private theorem term_rec (k : ℕ) :
    term (k+7) + 5 * term (k+5) + term (k+2) = 4 * term (k+6) + term (k+4) + 2 * term (k+3) := by
  unfold term
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => completion_rec k r

set_option maxRecDepth 100000 in
private theorem term_vals :
    term 1 = 41 ∧ term 2 = 76 ∧ term 3 = 108 ∧ term 4 = 170 ∧ term 5 = 257 ∧ term 6 = 398 := by
  decide +kernel

/-- The Fibonacci-type part of the closed form. -/
private def G : ℕ → ℤ
  | 0 => 29
  | 1 => 24
  | n+2 => G (n+1) + G n

private noncomputable def F (n : ℕ) : ℝ :=
  ((1 - Real.sqrt 5)^n * (-19 + 29 * Real.sqrt 5) +
    (1 + Real.sqrt 5)^n * (19 + 29 * Real.sqrt 5)) / (2^(n+1) * Real.sqrt 5)

private theorem F_eq_G (n : ℕ) : F n = G n := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [F, G]
    field_simp
    push_cast
    ring
  | one =>
    simp only [F, G]
    field_simp
    push_cast
    ring
  | more n ih₀ ih₁ =>
    have e : F (n+2) = F (n+1) + F n := by
      simp only [F]
      have hm : (1 - Real.sqrt 5)^2 = 2 * (1 - Real.sqrt 5) + 4 := by linear_combination hs
      have hp : (1 + Real.sqrt 5)^2 = 2 * (1 + Real.sqrt 5) + 4 := by linear_combination hs
      rw [pow_add (1 - Real.sqrt 5) n 2, pow_add (1 + Real.sqrt 5) n 2, hm, hp]
      field_simp
      ring
    rw [e, ih₀, ih₁]
    simp only [G]
    push_cast
    ring

private theorem term_closed (n : ℕ) (hn : 1 < n) :
    (term n : ℝ) = 5 + 4 * (1 + n) + (1 + n) * (2 + n) / 2 + G n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h6 : n ≤ 6
    · obtain ⟨t1, t2, t3, t4, t5, t6⟩ := term_vals
      interval_cases n <;> simp [t2, t3, t4, t5, t6, G] <;> norm_num
    · have r := term_rec (n-7)
      rw [show n-7+7=n by omega, show n-7+5=n-2 by omega, show n-7+2=n-5 by omega,
        show n-7+6=n-1 by omega, show n-7+4=n-3 by omega, show n-7+3=n-4 by omega] at r
      have r' : (term n : ℝ) + 5 * term (n-2) + term (n-5) =
          4 * term (n-1) + term (n-3) + 2 * term (n-4) := by exact_mod_cast r
      rw [ih (n-1) (by omega) (by omega), ih (n-2) (by omega) (by omega),
        ih (n-3) (by omega) (by omega), ih (n-4) (by omega) (by omega),
        ih (n-5) (by omega) (by omega)] at r'
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n-5, by omega⟩
      rw [show m+5-1 = m+4 by omega, show m+5-2 = m+3 by omega, show m+5-3 = m+2 by omega,
        show m+5-4 = m+1 by omega, show m+5-5 = m by omega] at r'
      have g1 : G (m+5) = G (m+4) + G (m+3) := rfl
      have g2 : G (m+4) = G (m+3) + G (m+2) := rfl
      have g3 : G (m+3) = G (m+2) + G (m+1) := rfl
      have g4 : G (m+2) = G (m+1) + G m := rfl
      have g1' : (G (m+5) : ℝ) = G (m+4) + G (m+3) := by exact_mod_cast g1
      have g2' : (G (m+4) : ℝ) = G (m+3) + G (m+2) := by exact_mod_cast g2
      have g3' : (G (m+3) : ℝ) = G (m+2) + G (m+1) := by exact_mod_cast g3
      have g4' : (G (m+2) : ℝ) = G (m+1) + G m := by exact_mod_cast g4
      push_cast at r' ⊢
      linear_combination r' - g1' + 3 * g2' - 3 * g3' + g4'

private theorem generating :
    ((1 - X)^3 * (1 - X - X^2)) * series =
      X * (41 - 88*X + 9*X^2 + 77*X^3 - 41*X^4 + X^5) := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := term_vals
  have L : ((1 - X)^3 * (1 - X - X^2)) * series =
      series - 4 * (X^1 * series) + 5 * (X^2 * series) - X^3 * series - 2 * (X^4 * series) +
        X^5 * series := by ring
  have R : (X : PowerSeries ℚ) * (41 - 88*X + 9*X^2 + 77*X^3 - 41*X^4 + X^5) =
      C (41:ℚ) * X^1 - C (88:ℚ) * X^2 + C (9:ℚ) * X^3 + C (77:ℚ) * X^4 - C (41:ℚ) * X^5 +
        C (1:ℚ) * X^6 := by
    simp only [map_ofNat, map_one]
    ring
  rw [L, R]
  ext n
  simp only [map_add, map_sub, coeff_X_pow_mul', series, coeff_mk,
    show ∀ f : PowerSeries ℚ, (4 : PowerSeries ℚ) * f = C (4:ℚ) * f from fun f => by
      rw [map_ofNat],
    show ∀ f : PowerSeries ℚ, (5 : PowerSeries ℚ) * f = C (5:ℚ) * f from fun f => by
      rw [map_ofNat],
    show ∀ f : PowerSeries ℚ, (2 : PowerSeries ℚ) * f = C (2:ℚ) * f from fun f => by
      rw [map_ofNat], coeff_C_mul]
  by_cases h : n ≤ 6
  · interval_cases n <;> simp [t1, t2, t3, t4, t5, t6, coeff_X] <;> norm_num
  · rw [if_neg (by omega : n ≠ 0), if_pos (by omega : 1 ≤ n), if_pos (by omega : 2 ≤ n),
      if_pos (by omega : 3 ≤ n), if_pos (by omega : 4 ≤ n), if_pos (by omega : 5 ≤ n),
      if_neg (by omega : n-1 ≠ 0), if_neg (by omega : n-2 ≠ 0), if_neg (by omega : n-3 ≠ 0),
      if_neg (by omega : n-4 ≠ 0), if_neg (by omega : n-5 ≠ 0)]
    simp only [coeff_X_pow, if_neg (by omega : n ≠ 1), if_neg (by omega : n ≠ 2),
      if_neg (by omega : n ≠ 3), if_neg (by omega : n ≠ 4), if_neg (by omega : n ≠ 5),
      if_neg (by omega : n ≠ 6), mul_zero, add_zero, sub_zero]
    have r := term_rec (n-7)
    rw [show n-7+7=n by omega, show n-7+5=n-2 by omega, show n-7+2=n-5 by omega,
      show n-7+6=n-1 by omega, show n-7+4=n-3 by omega, show n-7+3=n-4 by omega] at r
    have r' : (term n : ℚ) + 5 * term (n-2) + term (n-5) =
        4 * term (n-1) + term (n-3) + 2 * term (n-4) := by exact_mod_cast r
    linarith

private theorem recurrence (n : ℕ) (hn : 6 < n) :
    (term n : ℤ) = 4 * term (n-1) - 5 * term (n-2) + term (n-3) + 2 * term (n-4) - term (n-5) := by
  have r := term_rec (n-7)
  rw [show n-7+7=n by omega, show n-7+5=n-2 by omega, show n-7+2=n-5 by omega,
    show n-7+6=n-1 by omega, show n-7+4=n-3 by omega, show n-7+3=n-4 by omega] at r
  have r' : (term n : ℤ) + 5 * term (n-2) + term (n-5) =
      4 * term (n-1) + term (n-3) + 2 * term (n-4) := by exact_mod_cast r
  linarith

end IdempotentRows4

open OMA.S_oeis_a224671 in
theorem OMA.solution : type_of% @OMA.S_oeis_a224671.main := by
  refine ⟨IdempotentRows4.generating, ?_, IdempotentRows4.recurrence⟩
  intro n hn
  rw [IdempotentRows4.term_closed n hn]
  have h := IdempotentRows4.F_eq_G n
  simp only [IdempotentRows4.F] at h
  rw [← h]
  ring
