import OMAStatements.S_oeis_a188647
import Mathlib

/-!
# OEIS A188647: `a(n) = a(n-1) k - (k-1)/kⁿ` is an integer for `k = (√(x² + y) + x)²`, `y = ±1`

Put `s = √(x² + y)`, so `s² = x² + y` and `(s + x)(s - x) = y`. Hence

  `k = (s + x)²`,  `k⁻¹ = (s - x)²`  (their product is `y² = 1`),
  `k + k⁻¹ = 2 s² + 2 x² = 2 (2x² + y)`.

Applying the defining rule twice and eliminating the term `(k - 1) k⁻ⁿ⁻¹` gives

  `a(n+2) = (k + k⁻¹) a(n+1) - a(n) = 2 (2x² + y) a(n+1) - a(n)`,

with `a(0) = 1` and `a(1) = k - 1 + k⁻¹ = 2 (2x² + y) - 1`. So every `a(n)` is an integer.
-/

open OMA.S_oeis_a188647

namespace OMA.A188647

/-- `k ≠ 0` and `k + k⁻¹ = 2 (2x² + y)`. -/
lemma k_facts (x y : ℤ) (hx : 1 ≤ x) (hy : y = 1 ∨ y = -1) :
    k x y ≠ 0 ∧ k x y + (k x y)⁻¹ = 2 * (2 * (x : ℝ) ^ 2 + y) := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hnn : (0 : ℝ) ≤ (x : ℝ) ^ 2 + y := by
    rcases hy with rfl | rfl <;> push_cast <;> nlinarith
  have hy2 : (y : ℝ) ^ 2 = 1 := by
    rcases hy with rfl | rfl <;> norm_num
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt ((x : ℝ) ^ 2 + y) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = (x : ℝ) ^ 2 + y := by rw [hs]; exact Real.sq_sqrt hnn
  have hk : k x y = (s + x) ^ 2 := by unfold k; rw [hs]
  have hprod : (s + x) ^ 2 * (s - x) ^ 2 = 1 := by
    have h1 : (s + x) * (s - x) = y := by nlinarith
    calc (s + x) ^ 2 * (s - x) ^ 2 = ((s + x) * (s - x)) ^ 2 := by ring
      _ = 1 := by rw [h1, hy2]
  rw [hk]
  refine ⟨left_ne_zero_of_mul_eq_one hprod, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hprod]
  nlinarith

end OMA.A188647

open OMA.A188647 in
theorem OMA.solution : type_of% @OMA.S_oeis_a188647.main := by
  intro x y hx hy n
  obtain ⟨hK, hsum⟩ := k_facts x y hx hy
  have hmul : k x y * (k x y)⁻¹ = 1 := mul_inv_cancel₀ hK
  -- the defining rule, written with `k⁻¹`
  have hstep : ∀ n, a x y (n + 1)
      = a x y n * k x y - (k x y - 1) * (k x y)⁻¹ ^ (n + 1) := by
    intro n
    rw [a, div_eq_mul_inv, inv_pow]
  -- the three-term recurrence
  have hrec : ∀ n, a x y (n + 2) = (k x y + (k x y)⁻¹) * a x y (n + 1) - a x y n := by
    intro n
    have h1 := hstep (n + 1)
    have h2 := hstep n
    have e : (k x y)⁻¹ ^ (n + 1 + 1) = (k x y)⁻¹ * (k x y)⁻¹ ^ (n + 1) := by ring
    have h3 : (k x y - 1) * (k x y)⁻¹ ^ (n + 1) = a x y n * k x y - a x y (n + 1) := by
      linarith
    rw [h1, e]
    linear_combination (-(k x y)⁻¹) * h3 - (a x y n) * hmul
  have key : ∀ n : ℕ, ∃ z : ℤ, a x y n = z := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => exact ⟨1, by simp [a]⟩
    | one =>
      refine ⟨2 * (2 * x ^ 2 + y) - 1, ?_⟩
      have h0 : a x y 0 = 1 := by simp [a]
      rw [hstep 0, h0]
      push_cast
      linear_combination hsum - hmul
    | more n h0 h1 =>
      obtain ⟨m0, hm0⟩ := h0
      obtain ⟨m1, hm1⟩ := h1
      refine ⟨2 * (2 * x ^ 2 + y) * m1 - m0, ?_⟩
      rw [hrec, hsum, hm0, hm1]
      push_cast
      ring
  exact key n
