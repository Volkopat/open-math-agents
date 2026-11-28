import OMAStatements.S_mo_351449
import Mathlib

-- Problem: mo-351449, if |a_ij| <= b_ij entrywise and the spectral radii of a and b are equal,
-- is a = e^{i phi} b for a single phase phi?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take a = diag(1, 0) and b = the 2 x 2 identity. Both have spectral radius 1 and
-- |a_ij| <= b_ij, but a_11 = 0 while e^{i phi} b_11 is never 0.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_351449.main) := by
  intro h
  have hb : (1 : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hle : ∀ i j, ‖(Matrix.diagonal ![(1 : ℂ), 0]) i j‖ ≤
      (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  have hrad : spectralRadius ℂ (Matrix.diagonal ![(1 : ℂ), 0]) =
      spectralRadius ℂ ((1 : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ)) := by
    rw [hb, spectrum.spectralRadius_one, spectralRadius, spectrum_diagonal, iSup_range]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i <;> simp
    · exact le_iSup_of_le 0 (by simp)
  obtain ⟨φ, _, hφ⟩ := h 2 (Matrix.diagonal ![(1 : ℂ), 0]) 1 hle hrad
  have h11 := hφ 1 1
  simp at h11
  exact Complex.exp_ne_zero _ h11.symm
