import OMAStatements.S_mo_478522
import Mathlib

namespace Wave10JEntropy
open Matrix
open OMA.S_mo_478522

noncomputable def C : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 5/8; 0, 1, 3/4; 5/8, 3/4, 1]

theorem symmetric : C.IsSymm := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem positive : C.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  intro v hv
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, C]
  by_contra! h
  have h₀ : v 2 = 0 := by
    by_contra hh
    nlinarith [sq_nonneg (v 0 + 5/8*v 2), sq_nonneg (v 1 + 3/4*v 2),
               sq_pos_of_ne_zero hh]
  rw [h₀] at h
  have ha : v 0 = 0 := by
    by_contra hh
    nlinarith [sq_pos_of_ne_zero hh, sq_nonneg (v 1)]
  have hb : v 1 = 0 := by
    by_contra hh
    nlinarith [sq_pos_of_ne_zero hh, sq_nonneg (v 0)]
  exact hv (by ext i; fin_cases i <;> assumption)

noncomputable def x : Fin 3 → ℝ := ![1/5,1/5,3/5]
noncomputable def y : Fin 3 → ℝ := ![2/5,2/5,1/5]

theorem inX : x ∈ simplex 3 := by
  constructor
  · intro i; fin_cases i <;> norm_num [x]
  · norm_num [x, Fin.sum_univ_three, Matrix.cons_val_two]
theorem inY : y ∈ simplex 3 := by
  constructor
  · intro i; fin_cases i <;> norm_num [y]
  · norm_num [y, Fin.sum_univ_three, Matrix.cons_val_two]

theorem fails : ¬ ConvexOn ℝ (simplex 3) (entropy C) := by
  intro h
  have hmid := h.2 inX inY (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  norm_num [entropy, C, x, y, Fin.sum_univ_three, Pi.add_apply, Matrix.cons_val_two, Pi.smul_apply, smul_eq_mul] at hmid
  have he := Real.log_lt_log
    (show 0 < (23/40:ℝ)*(13/20)*(7/8)^3*(21/40)^2*(11/20)^2*(3/4) by norm_num)
    (show (23/40:ℝ)*(13/20)*(7/8)^3*(21/40)^2*(11/20)^2*(3/4) <
      (11/20:ℝ)^3*(3/5)^3*(13/16)^4 by norm_num)
  simp (disch := norm_num) only [Real.log_mul, Real.log_pow] at he
  norm_num at he
  linarith

end Wave10JEntropy

open Wave10JEntropy

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_478522.main) := by
  intro h
  apply fails
  apply h 3 C symmetric positive
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num [C]
  · intro i; fin_cases i <;> rfl

