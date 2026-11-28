import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Moore–Penrose inverse bound near the identity

Source: https://mathoverflow.net/questions/254890/is-the-following-inequality-true-for-the-norm-of-moore-penrose-pseudoinverses
Question by Mathguest, 17 November 2016 (CC BY-SA 3.0).
Credit: @etaubman

Fedor Petrov observed in the source comments that the strict operator-norm
condition already forces invertibility. This is a formalization of that known
answer, not a claim of a new result. The norm below is the Euclidean (l2)
operator norm, not an entrywise norm. All four Penrose equations are stated.
-/

open scoped Matrix Matrix.Norms.L2Operator

namespace OMA.S_mo_254890

def IsMoorePenrose {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  L * M * L = L ∧ M * L * M = M ∧
    (L * M)ᵀ = L * M ∧ (M * L)ᵀ = M * L

theorem main : ∀ (n : ℕ) (L M : Matrix (Fin n) (Fin n) ℝ),
    L.PosSemidef → IsMoorePenrose L M → ‖1 - L‖ < 1 →
      ‖M‖ ≤ 1 / (1 - ‖1 - L‖) := by
  sorry

end OMA.S_mo_254890
