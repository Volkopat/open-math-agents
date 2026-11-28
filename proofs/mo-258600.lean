import OMAStatements.S_mo_258600
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_258600.main) := fun h => by
  obtain ⟨M, hM⟩ := h ℤ (ZMod 5) (Int.castRingHom _) (ZMod.ringHom_surjective _) 2 one_lt_two
    ⟨!![2, 0; 0, 1], !![3, 0; 0, 1], by decide, by decide⟩
  have := congrArg (fun A : (Matrix (Fin 2) (Fin 2) (ZMod 5))ˣ => (A.1).det) hM
  change ((Int.castRingHom (ZMod 5)).mapMatrix M.1).det = Matrix.det !![2, 0; 0, 1] at this
  rw [← RingHom.map_det, Matrix.det_fin_two_of] at this
  rcases Int.isUnit_iff.1 ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit) with e | e <;> rw [e] at this <;> revert this <;> decide
