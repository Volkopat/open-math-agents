import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Hadamard l2 sum of correlation matrices need not be positive semidefinite

Source: https://mathoverflow.net/questions/336099/hadamard-ell-p-sum-of-two-symmetric-positive-semidefinite-matrices-follow-up
Question by D_809, 2019-07-14 (CC BY-SA 4.0).
Credit: @etaubman

This is a complete formalization of fedja's counterexample in the source comment
of 2019-07-15: the quadratic forms (x1+x2)^2+(x3+x4)^2 and
(x1+x3)^2+(x2+x4)^2 and test vector (1,-1,-1,1). No novelty is claimed.
-/

namespace OMA.S_mo_336099

open Matrix
open scoped BigOperators Matrix

noncomputable def hadamardL2 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => Real.sqrt (A i j ^ 2 + B i j ^ 2)

def conjecture : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (A B : Matrix (Fin n) (Fin n) ℝ),
    A.PosSemidef → B.PosSemidef →
    (∀ i j, 0 ≤ A i j) → (∀ i j, 0 ≤ B i j) →
    (∀ i, A i i = 1) → (∀ i, B i i = 1) →
    (hadamardL2 A B).PosSemidef

theorem main : conjecture := by
  sorry

end OMA.S_mo_336099
