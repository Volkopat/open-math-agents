import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A dimension-dependent threshold for a dominant nonnegative matrix

Source: https://mathoverflow.net/questions/91250
Question by Sasho Nikolov. Formalization and proof prepared for @etaubman.

The source allows every submatrix size from one to n. The explicit threshold K = n
suffices: a nonzero entry of B gives a one-by-one witness, while B = 0 permits the
whole matrix A. This does not assert a dimension-independent threshold or settle the
separate special case K = 2 in every dimension.
-/

open scoped BigOperators

namespace OMA.S_mo_91250

def Dominates {n : ℕ} (K : ℝ) (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, B i j ≠ 0 → ∀ r s, K * A r s ≤ B i j

def HasLargeSubmatrix {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k ≤ n ∧
    ∃ r c : Fin k → Fin n, Function.Injective r ∧ Function.Injective c ∧
      |A.det| ^ (1 / (n : ℝ)) ≤ |((A + B).submatrix r c).det| ^ (1 / (k : ℝ))

theorem main :
    ∀ n : ℕ, 0 < n → ∃ K : ℝ, 0 < K ∧
      ∀ K' : ℝ, K ≤ K' →
      ∀ A B : Matrix (Fin n) (Fin n) ℝ,
        (∀ i j, 0 ≤ A i j) → (∀ i j, 0 ≤ B i j) →
        Dominates K' A B → HasLargeSubmatrix A B := by
  sorry

end OMA.S_mo_91250
