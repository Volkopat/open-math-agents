import OMAReductions.R_mo_46445_R1
import Mathlib

/-! `x ↦ cot ((x + c) t)` has derivative `-t / sin ((x + c) t)^2 < 0` wherever the sine is nonzero,
so it is strictly decreasing on any interval free of zeros of the sine. -/

namespace OMA.Step_mo_46445_R1_H2

open Real Set

lemma affine_cot_deriv (c t x : ℝ) (h : sin ((x + c) * t) ≠ 0) :
    HasDerivAt (fun y => cot ((y + c) * t)) (-(t / sin ((x + c) * t) ^ 2)) x := by
  let z := (x + c) * t
  have hz : sin z ≠ 0 := h
  have hd := (hasDerivAt_cos z).div (hasDerivAt_sin z) hz
  have ha : HasDerivAt (fun y : ℝ => (y + c) * t) t x := by
    simpa using (((hasDerivAt_id x).add_const c).mul_const t)
  have hc := hd.comp x ha
  have hn : -sin z * sin z - cos z * cos z = -1 := by
    nlinarith only [sin_sq_add_cos_sq z]
  have he : (-sin z * sin z - cos z * cos z) / sin z ^ 2 * t = -(t / sin z ^ 2) := by
    rw [hn]
    ring
  rw [he] at hc
  simpa [Function.comp_def, cot_eq_cos_div_sin, z] using hc

theorem strictAntiOn_affine_cot : OMA.R_mo_46445_R1.H2 := by
  intro a b c t ht h
  apply strictAntiOn_of_deriv_neg (convex_Ioo a b)
  · intro x hx
    exact (affine_cot_deriv c t x (h x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(affine_cot_deriv c t x (h x hx)).deriv]
    exact neg_lt_zero.mpr (div_pos ht (sq_pos_of_ne_zero (h x hx)))

end OMA.Step_mo_46445_R1_H2

theorem OMA.solution : OMA.R_mo_46445_R1.H2 :=
  OMA.Step_mo_46445_R1_H2.strictAntiOn_affine_cot
