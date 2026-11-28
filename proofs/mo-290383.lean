import OMAStatements.S_mo_290383
import Mathlib

-- Problem: mo-290383, is every nonnegative matrix of rank 2r a difference of two nonnegative
-- matrices of rank at most r?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No: the 2 x 2 identity matrix (rank 2, r = 1) is a counterexample. If 1 = P - Q with Q
-- nonnegative and both of rank at most 1, then det Q = 0 and
-- det P = det (1 + Q) = 1 + trace Q + det Q >= 1, so P is invertible and has rank 2.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_290383.main) := by
  intro h
  have hrank : (1 : Matrix (Fin 2) (Fin 2) ℚ).rank = 2 * 1 := by simp
  have hnn : OMA.S_mo_290383.Nonnegative (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs <;> norm_num
  obtain ⟨P, Q, _, hQ, hPr, hQr, hM⟩ := h 2 1 1 hnn hrank
  have hdet : ∀ A : Matrix (Fin 2) (Fin 2) ℚ, A.rank ≤ 1 → A.det = 0 := by
    intro A hA
    by_contra hne
    have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hne)
    have h2 := Matrix.rank_of_isUnit A hu
    rw [Fintype.card_fin] at h2
    omega
  have hdP := hdet P hPr
  have hdQ := hdet Q hQr
  have hPQ : P = 1 + Q := sub_eq_iff_eq_add.mp hM.symm
  rw [hPQ, Matrix.det_fin_two] at hdP
  rw [Matrix.det_fin_two] at hdQ
  simp [Matrix.add_apply] at hdP
  nlinarith [hQ 0 0, hQ 1 1]
