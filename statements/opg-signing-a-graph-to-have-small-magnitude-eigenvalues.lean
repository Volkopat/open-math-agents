import Mathlib

/-!
# Signing a graph to have small magnitude eigenvalues

Source: https://www.openproblemgarden.org/op/signing_a_graph_to_have_small_magnitude_eigenvalues
Credit: @ishaanzee

**Conjecture** (Y. Bilu, N. Linial). If `A` is the adjacency matrix of a `d`-regular graph, then
there is a symmetric signing of `A` (i.e. replace some `+1` entries by `-1`) so that the resulting
matrix has all eigenvalues of magnitude at most `2 √(d - 1)`.

Formalization:
* Graphs are finite simple graphs; `d`-regular is `IsRegularOfDegree d`. We take `d ≥ 1`.
* A symmetric signing is a choice of signs `σ u v ∈ {1, -1}` with `σ u v = σ v u`; the signed
  matrix has entry `σ u v` when `u` and `v` are adjacent and `0` otherwise. It is a real symmetric
  (Hermitian) matrix, and its eigenvalues are Mathlib's `Matrix.IsHermitian.eigenvalues`.
-/

namespace OMA.S_opg_signing_a_graph_to_have_small_magnitude_eigenvalues

/-- The adjacency matrix of `G` signed by `σ`. -/
noncomputable def signedAdj {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : V → V → ℝ) :
    Matrix V V ℝ :=
  Matrix.of fun u v => if G.Adj u v then σ u v else 0

/-- **Bilu–Linial conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ), 1 ≤ d → G.IsRegularOfDegree d →
      ∃ σ : V → V → ℝ, (∀ u v, σ u v = 1 ∨ σ u v = -1) ∧ (∀ u v, σ u v = σ v u) ∧
        ∃ h : (signedAdj G σ).IsHermitian, ∀ i, |h.eigenvalues i| ≤ 2 * Real.sqrt (d - 1) := by
  sorry

end OMA.S_opg_signing_a_graph_to_have_small_magnitude_eigenvalues
