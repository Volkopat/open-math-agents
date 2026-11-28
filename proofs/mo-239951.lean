import OMAStatements.S_mo_239951
import Mathlib

open OMA.S_mo_239951 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_239951.main) := fun h => by
  let G : SimpleGraph (Fin 8) := { Adj i j := i.val % 2 ≠ j.val % 2 }
  have hd : ∀ i, G.degree i = 4 := by decide
  have := h _ G (by decide) (-3/5) (fun i => (-1)^i.val) (fun e => by simpa using congrFun e 0) (funext fun i => by fin_cases i <;> simp [transition, hd, Matrix.mulVec, dotProduct, Fin.sum_univ_eight, G] <;> norm_num)
  norm_num at this
