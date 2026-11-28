import Mathlib

/-!
# Eigenvalues in the unit disk for a 2×2 block perturbation

Ivano asks whether sufficiently small positive perturbations stabilize the
block matrix, including the case of commuting lower blocks. The hypothesis
on `A` uses the formulation in the question with a simple eigenvalue at one
and all remaining eigenvalues in the open unit disk.

Source: https://mathoverflow.net/questions/393199
-/

namespace OMA.S_mo_393199

/-- All complex eigenvalues of a real matrix lie in the open unit disk. -/
def stable {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ z : ℂ, Polynomial.aeval z M.charpoly = 0 → ‖z‖ < 1

/-- The perturbed block matrix from the question. -/
noncomputable def block {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) (e : ℝ) :=
  Matrix.fromBlocks (A - e • 1) 1 (-e • C) B

/-- Does stability hold for all sufficiently small positive perturbations, even when
the positive semidefinite lower-left coefficient commutes with the lower-right block? -/
theorem main : ∀ (n : ℕ) (A B C : Matrix (Fin n) (Fin n) ℝ),
    A.charpoly.rootMultiplicity 1 = 1 →
    (∀ z : ℂ, Polynomial.aeval z A.charpoly = 0 → z ≠ 1 → ‖z‖ < 1) →
    stable B → C.PosSemidef → Commute B C →
      ∃ δ : ℝ, 0 < δ ∧ ∀ e ∈ Set.Ioo 0 δ, stable (block A B C e) := by
  sorry

end OMA.S_mo_393199
