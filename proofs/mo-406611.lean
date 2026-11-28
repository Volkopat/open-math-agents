import OMAStatements.S_mo_406611
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_406611.main) := fun h => by
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 0; 0, 1, 0]
  have e : (1 - A) * (1 + A) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
  rcases h 3 A (by simp [A, Fin.forall_fin_succ]) (by simp [A, Fin.forall_fin_succ])
    (fun h0 => by simpa [h0] using congrArg Matrix.det e)
    (by rw [Matrix.inv_eq_right_inv e]; ext i j; fin_cases i <;> fin_cases j <;> simp [A]) with h | h
  · simpa [A] using h (show (1 : Fin 3) < 2 by decide)
  · simpa [A] using h (show OrderDual.toDual (1 : Fin 3) < OrderDual.toDual 0 by decide)
