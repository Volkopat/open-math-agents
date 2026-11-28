import OMAStatements.S_mo_371412
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_371412.main := by
  intro n M k hk h hp
  have u : IsUnit M.det := .of_pow_eq_one (by rw [← Matrix.det_pow, h, Matrix.det_one]) (by omega)
  have : ((M.det : ℤ) : ZMod 2) = (M.permanent : ZMod 2) := by
    simp only [Matrix.det_apply, Matrix.permanent, Int.cast_sum, Units.smul_def, Int.cast_prod, zsmul_eq_mul, Int.cast_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rcases Int.isUnit_iff.1 u with e | e <;> simp [e, hp] at this
