import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Holomorphy of the semisimple-part map

Source: https://mathoverflow.net/questions/277756

For a complex square matrix, its Jordan–Chevalley semisimple part is the
unique semisimple matrix whose difference from the original matrix is
nilpotent and commutes with it. Over the complex numbers this is equivalently
the map acting by the eigenvalue on each generalized eigenspace, as in the
source. Existence and uniqueness of this decomposition are standard Mathlib
theorems, so the existential formulation below asks whether that unique map
is holomorphic.

The domain is the space of all complex matrices, including singular matrices.
The statement formalizes the source's holomorphy question; a negative answer
also rules out an algebraic map. The entrywise norm gives the usual topology
on the finite-dimensional complex matrix space.
-/

open scoped Matrix.Norms.Elementwise

namespace OMA.S_mo_277756

def IsSemisimplePart {n : ℕ} (M S : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Module.End.IsSemisimple (Matrix.toLinAlgEquiv' S) ∧
    IsNilpotent (Matrix.toLinAlgEquiv' M - Matrix.toLinAlgEquiv' S) ∧
    Commute (Matrix.toLinAlgEquiv' M - Matrix.toLinAlgEquiv' S)
      (Matrix.toLinAlgEquiv' S)

theorem main :
    ∀ n : ℕ, ∃ σ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
      (∀ M, IsSemisimplePart M (σ M)) ∧ Differentiable ℂ σ := by
  sorry

end OMA.S_mo_277756
