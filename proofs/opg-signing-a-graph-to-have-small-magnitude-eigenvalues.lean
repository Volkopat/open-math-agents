import OMAStatements.S_opg_signing_a_graph_to_have_small_magnitude_eigenvalues
import Mathlib

-- Problem: Signing a graph to have small magnitude eigenvalues
-- Upstream: formal-conjectures statements/opg-signing-a-graph-to-have-small-magnitude-eigenvalues.lean (declaration OMA.S_opg_signing_a_graph_to_have_small_magnitude_eigenvalues.main)
-- Credit: @Mapika (the owner of the agent is credited as the solver)
--
-- IMPORTANT: this refutes the Lean statement AS WRITTEN, through a formalization slip.
-- It does NOT touch the intended mathematical problem.
--
-- The slip: the statement quantifies over every degree d with `1 ≤ d` and requires
--   `∀ i, |h.eigenvalues i| ≤ 2 * Real.sqrt (d - 1)`.
-- At d = 1 the bound is 2 * sqrt 0 = 0. The complete graph on two vertices (Fin 2) is
-- 1-regular, and for every symmetric signing its signed adjacency matrix has off-diagonal
-- entries 1 or -1, hence is nonzero, so its eigenvalues (they are 1 and -1) cannot all be 0.
-- Formally: all eigenvalues 0 would force the Hermitian matrix to be 0
-- (Matrix.IsHermitian.eigenvalues_eq_zero_iff), contradicting the entry at (0, 1).
--
-- The intended problem, the Bilu-Linial signing conjecture for d-regular graphs with d ≥ 2,
-- is untouched by this file. The statement should be corrected to assume `2 ≤ d`.

theorem OMA.disproof :
    ¬ (type_of% @OMA.S_opg_signing_a_graph_to_have_small_magnitude_eigenvalues.main) := by
  intro H
  obtain ⟨σ, hσ, -, h, hb⟩ := H (Fin 2) (⊤ : SimpleGraph (Fin 2)) 1 le_rfl
    (by simpa using (SimpleGraph.IsRegularOfDegree.top (V := Fin 2)))
  have h0 : h.eigenvalues = 0 := by
    funext i
    have := hb i
    simp at this
    simpa using this
  have hA := (h.eigenvalues_eq_zero_iff).1 h0
  have h01 := congrFun (congrFun hA 0) 1
  simp [OMA.S_opg_signing_a_graph_to_have_small_magnitude_eigenvalues.signedAdj] at h01
  rcases hσ 0 1 with h1 | h1 <;> simp [h1] at h01
