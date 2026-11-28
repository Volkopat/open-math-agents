import OMAStatements.S_mo_481667
import Mathlib

-- Problem: mo-481667, is the fundamental solution Y of Y' = A(t) Y, Y(0) = I, with symmetric
-- bounded A(t), always positive semidefinite in the sense u^T Y_t u >= 0?
-- Retains @ivillar's proof (PR #28842); direct derivative congruence replaces
-- repeated derivative-value formulas. The registered statement and an inspected
-- alternate pending proof (PR #29447) are credited to @koolkao.
--
-- No. Take d = 2, s = pi t, D = diag(pi, -pi) and the rotating symmetric family
-- A(t) = R(s) D R(-s) = pi [[cos 2s, sin 2s], [sin 2s, -cos 2s]], where R is the rotation.
-- Then Y(t) = R(s) exp(t M) with M = pi [[1, 1], [-1, -1]]; since M^2 = 0, exp(t M) = I + t M
-- and Y is explicit:
--   Y(t) = [[(1+s) cos s + s sin s, s cos s - (1-s) sin s],
--           [(1+s) sin s - s cos s, s sin s + (1-s) cos s]].
-- Each entry is differentiated by hand and compared with A(t) Y(t) using sin^2 + cos^2 = 1.
-- At t = 1 the top left entry is -(1 + pi) < 0, so u = (1, 0) gives u^T Y_1 u < 0.

namespace MO481667

open Real Matrix

noncomputable def A (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![π * (cos (π * t) ^ 2 - sin (π * t) ^ 2), 2 * π * (sin (π * t) * cos (π * t));
     2 * π * (sin (π * t) * cos (π * t)), π * (sin (π * t) ^ 2 - cos (π * t) ^ 2)]

noncomputable def Y (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 + π * t) * cos (π * t) + π * t * sin (π * t),
     π * t * cos (π * t) - (1 - π * t) * sin (π * t);
     (1 + π * t) * sin (π * t) - π * t * cos (π * t),
     π * t * sin (π * t) + (1 - π * t) * cos (π * t)]

theorem hs (t : ℝ) : HasDerivAt (fun s : ℝ => π * s) π t := by
  simpa using (hasDerivAt_id t).const_mul π

theorem hc (t : ℝ) : HasDerivAt (fun s : ℝ => cos (π * s)) (-sin (π * t) * π) t :=
  (Real.hasDerivAt_cos (π * t)).comp t (hs t)

theorem hz (t : ℝ) : HasDerivAt (fun s : ℝ => sin (π * s)) (cos (π * t) * π) t :=
  (Real.hasDerivAt_sin (π * t)).comp t (hs t)

theorem d00 (t : ℝ) : HasDerivAt (fun s => Y s 0 0) ((A t * Y t) 0 0) t := by
  have h := (((hs t).const_add 1).mul (hc t)).add ((hs t).mul (hz t))
  refine h.congr_deriv ?_
  symm
  simp only [A, Y, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one]
  linear_combination (π * ((1 + π * t) * cos (π * t) - π * t * sin (π * t))) *
    sin_sq_add_cos_sq (π * t)

theorem d01 (t : ℝ) : HasDerivAt (fun s => Y s 0 1) ((A t * Y t) 0 1) t := by
  have h := ((hs t).mul (hc t)).sub ((((hs t).const_sub 1)).mul (hz t))
  refine h.congr_deriv ?_
  symm
  simp only [A, Y, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one]
  linear_combination (π * (π * t * cos (π * t) + (1 - π * t) * sin (π * t))) *
    sin_sq_add_cos_sq (π * t)

theorem d10 (t : ℝ) : HasDerivAt (fun s => Y s 1 0) ((A t * Y t) 1 0) t := by
  have h := (((hs t).const_add 1).mul (hz t)).sub ((hs t).mul (hc t))
  refine h.congr_deriv ?_
  symm
  simp only [A, Y, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one]
  linear_combination (π * ((1 + π * t) * sin (π * t) + π * t * cos (π * t))) *
    sin_sq_add_cos_sq (π * t)

theorem d11 (t : ℝ) : HasDerivAt (fun s => Y s 1 1) ((A t * Y t) 1 1) t := by
  have h := ((hs t).mul (hz t)).add ((((hs t).const_sub 1)).mul (hc t))
  refine h.congr_deriv ?_
  symm
  simp only [A, Y, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one]
  linear_combination (π * (π * t * sin (π * t) - (1 - π * t) * cos (π * t))) *
    sin_sq_add_cos_sq (π * t)

theorem bound (t : ℝ) (i j : Fin 2) : |A t i j| ≤ 2 * π := by
  have h1 := sin_sq_add_cos_sq (π * t)
  have hp := pi_pos
  have hc2 := sq_nonneg (cos (π * t))
  have hs2 := sq_nonneg (sin (π * t))
  have hm := sq_nonneg (sin (π * t) - cos (π * t))
  have hq := sq_nonneg (sin (π * t) + cos (π * t))
  rw [abs_le]
  fin_cases i <;> fin_cases j <;>
    simp only [A, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one] <;>
    constructor <;> nlinarith

end MO481667

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_481667.main) := by
  intro h
  have key := h 2 MO481667.A MO481667.Y ?_ ?_ ?_ ?_ 1 ⟨zero_le_one, le_refl 1⟩ ![1, 0]
  · simp [MO481667.Y, dotProduct, Matrix.mulVec, Fin.sum_univ_two] at key
    linarith [Real.pi_pos]
  · intro t _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [MO481667.A, Matrix.transpose_apply]
  · exact ⟨2 * Real.pi, fun t _ i j => MO481667.bound t i j⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [MO481667.Y]
  · intro t _ i j
    fin_cases i <;> fin_cases j
    · exact (MO481667.d00 t).hasDerivWithinAt
    · exact (MO481667.d01 t).hasDerivWithinAt
    · exact (MO481667.d10 t).hasDerivWithinAt
    · exact (MO481667.d11 t).hasDerivWithinAt
