import OMAStatements.S_mo_427947
import Mathlib

open Matrix in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_427947.main) := fun h => by
  have e : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = !![0, 1; 1, 0] :=
    inv_eq_right_inv (by simp [one_fin_two])
  have := congrFun (h 2 !![1, 1; 0, 1] !![0, 1; 1, 0] (by ext i j; fin_cases i <;> fin_cases j <;> simp) (by simp)
    (by rw [e]; ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, vecMul, dotProduct, Fin.sum_univ_two, conjTranspose_apply])
    (by simp) (fun h => by simpa [mul_apply, Fin.sum_univ_two] using congrFun (congrFun h 1) 1)
    1 ![1, 0] (by simp) (by simp) (by ext i; fin_cases i <;> simp)) 1
  simp at this
