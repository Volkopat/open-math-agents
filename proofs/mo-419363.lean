import OMAStatements.S_mo_419363
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_419363.main := by
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  exact ⟨Matrix (Fin 2) (Fin 2) ℂ, inferInstance, inferInstance, FiniteDimensional.complete ℂ _,
    ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], fun h => by simpa [Matrix.mul_fin_two] using congrFun (congrFun h 0) 0⟩,
    fun _ _ h => mul_eq_one_comm.1 h⟩
