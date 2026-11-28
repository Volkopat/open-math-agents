import Mathlib

/-!
# Generic rank of a weighted projected matrix

KOE, MathOverflow question 279516 (2017).
https://mathoverflow.net/questions/279516 (CC BY-SA 3.0).

The joint distribution of all entries of the input matrix is taken to be
absolutely continuous with respect to entrywise Lebesgue measure. For a
subset of columns, the bound adds the number of omitted columns to the
dimension of the sum of the possible column spaces of the retained columns.
-/

open MeasureTheory

namespace OMA.S_mo_279516

variable {n k : ℕ}

noncomputable instance matrixMeasureSpace : MeasureSpace (Matrix (Fin n) (Fin k) ℝ) :=
  inferInstanceAs (MeasureSpace (Fin n → Fin k → ℝ))

def transformed (Q : Matrix (Fin n) (Fin n) ℝ) (C Y : Matrix (Fin n) (Fin k) ℝ) :=
  (Q * Y).hadamard C

noncomputable def columnSpace (Q : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin k) ℝ) (j : Fin k) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.range ((Matrix.diagonal (fun i => C i j) * Q).mulVecLin)

noncomputable def bound (Q : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin k) ℝ) (J : Finset (Fin k)) : ℕ :=
  k - J.card + Module.finrank ℝ ↥(J.sup (columnSpace Q C))

theorem main :
    ∀ {n k : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin k) ℝ),
    Q * Q = Q → (∀ i j, 0 < C i j) →
    ∀ μ : Measure (Matrix (Fin n) (Fin k) ℝ), μ ≪ volume →
    ∀ᵐ Y ∂μ, IsLeast (Set.range (bound Q C)) (transformed Q C Y).rank := by
  sorry

end OMA.S_mo_279516
