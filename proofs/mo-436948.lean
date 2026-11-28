import OMAStatements.S_mo_436948
import Mathlib

-- Problem: mo-436948, does the two-sided quadratic bound
-- |f(x) - f(x0) - <grad f(x0), x - x0>| <= (L/2) |x - x0|^2 imply that grad f is L-Lipschitz,
-- without convexity?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Yes. Fix x, y, put D = g(y) - g(x) (g the gradient), A = (y - x)/2, B = s D, and use the
-- bound four times: at the points p = x + A - B and q = x + A + B, each with base points x and
-- y. Adding the four inequalities, the values of f cancel and the parallelogram law gives
--   2 <D, B> <= 2 L (|A|^2 + |B|^2),  i.e.  2 s |D|^2 <= (L/2) |y - x|^2 + 2 L s^2 |D|^2.
-- With s = 1/(2L) this is |D|^2 <= L^2 |y - x|^2 (and for L = 0, s = 1 gives D = 0).
-- The argument works for any map g satisfying the bound; differentiability is not needed.

namespace MO436948

theorem key {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → E) (L : ℝ)
    (H : ∀ x x₀ : E, |f x - (f x₀ + inner ℝ (g x₀) (x - x₀))| ≤ L / 2 * ‖x - x₀‖ ^ 2)
    (x y A B : E) (hy : y = x + A + A) :
    2 * inner ℝ (g y - g x) B ≤ L / 2 * (4 * (‖A‖ ^ 2 + ‖B‖ ^ 2)) := by
  have h1 := H (x + A - B) x
  have h2 := H (x + A - B) y
  have h3 := H (x + A + B) y
  have h4 := H (x + A + B) x
  have e1 : x + A - B - x = A - B := by abel
  have e2 : x + A - B - y = -(A + B) := by
    rw [hy]
    abel
  have e3 : x + A + B - y = B - A := by
    rw [hy]
    abel
  have e4 : x + A + B - x = A + B := by abel
  rw [e1, abs_le, inner_sub_right] at h1
  rw [e2, abs_le, norm_neg, inner_neg_right, inner_add_right] at h2
  rw [e3, abs_le, norm_sub_rev, inner_sub_right] at h3
  rw [e4, abs_le, inner_add_right] at h4
  have par : ‖A + B‖ ^ 2 + ‖A - B‖ ^ 2 = 2 * (‖A‖ ^ 2 + ‖B‖ ^ 2) := by
    have h := parallelogram_law_with_norm ℝ A B
    simp only [sq]
    linarith
  have par' : L / 2 * ‖A + B‖ ^ 2 + L / 2 * ‖A - B‖ ^ 2 =
      L / 2 * (2 * (‖A‖ ^ 2 + ‖B‖ ^ 2)) := by
    rw [← mul_add, par]
  rw [inner_sub_left]
  linarith [h1.1, h2.2, h3.1, h4.2, par']

theorem core {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (g : E → E) (L : ℝ)
    (H : ∀ x x₀ : E, |f x - (f x₀ + inner ℝ (g x₀) (x - x₀))| ≤ L / 2 * ‖x - x₀‖ ^ 2)
    (x y : E) (s : ℝ) :
    2 * s * ‖g y - g x‖ ^ 2 ≤ L / 2 * ‖y - x‖ ^ 2 + 2 * L * s ^ 2 * ‖g y - g x‖ ^ 2 := by
  have hy : y = x + (1 / 2 : ℝ) • (y - x) + (1 / 2 : ℝ) • (y - x) := by
    rw [add_assoc, ← add_smul]
    norm_num
  have k := key f g L H x y ((1 / 2 : ℝ) • (y - x)) (s • (g y - g x)) hy
  simp only [inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] at k
  nlinarith [k]

theorem real_step (L N U : ℝ) (hL : 0 ≤ L)
    (c : ∀ s : ℝ, 2 * s * N ≤ L / 2 * U + 2 * L * s ^ 2 * N) : N ≤ L ^ 2 * U := by
  rcases hL.lt_or_eq with hpos | h0
  · have c1 := c (1 / (2 * L))
    have hs : 2 * L * (1 / (2 * L)) = 1 := by
      field_simp
    have m := mul_le_mul_of_nonneg_left c1 (by positivity : (0 : ℝ) ≤ 2 * L)
    have t1 : 2 * L * (2 * (1 / (2 * L)) * N) = 2 * N := by
      calc 2 * L * (2 * (1 / (2 * L)) * N) = 2 * (2 * L * (1 / (2 * L))) * N := by ring
        _ = 2 * N := by rw [hs]; ring
    have t2 : 2 * L * (L / 2 * U + 2 * L * (1 / (2 * L)) ^ 2 * N) = L ^ 2 * U + N := by
      calc 2 * L * (L / 2 * U + 2 * L * (1 / (2 * L)) ^ 2 * N)
          = L ^ 2 * U + (2 * L * (1 / (2 * L))) ^ 2 * N := by ring
        _ = L ^ 2 * U + N := by rw [hs]; ring
    rw [t1, t2] at m
    linarith
  · have c1 := c 1
    rw [← h0] at c1 ⊢
    linarith

end MO436948

theorem OMA.solution : type_of% @OMA.S_mo_436948.main := by
  intro n f L _ H
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  have c := MO436948.core f (gradient f) L H y x
  have hN := MO436948.real_step L _ _ hL c
  rw [← mul_pow] at hN
  have h3 := sq_le_sq.mp hN
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hL (norm_nonneg _))] at h3
