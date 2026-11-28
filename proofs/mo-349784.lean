import OMAStatements.S_mo_349784
import Mathlib

open OMA.S_mo_349784 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_349784.main) := fun h => by
  have := (h (Fin 2) 3 (fun _ => 1) (fun _ => one_pos) ![{0}, {1}, {0, 1}] (by decide) (by decide)).det_pos
  simp [Matrix.det_fin_three, gram] at this; linarith
