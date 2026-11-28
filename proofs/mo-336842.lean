import OMAStatements.S_mo_336842
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_336842.main) := fun h => by
  have I : OMA.S_mo_336842.IsIrreducible (1 : Matrix (Fin 1) (Fin 1) ℝ) := fun i j => ⟨1, one_pos, by fin_cases i; fin_cases j; simp⟩
  obtain ⟨σ, hσ⟩ := h 1 1 1 (-1) (by simp) (by simp) I I (by simp) (by simp)
  have := hσ 0 0
  norm_num [Subsingleton.elim (σ 0) 0] at this
