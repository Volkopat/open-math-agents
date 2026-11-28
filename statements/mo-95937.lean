import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith

/-!
# Copositivity of a constant matrix minus a positive semidefinite matrix

Source: https://mathoverflow.net/questions/95937/copositive-matrix
Question by Felix Goldberg, 2012-05-03 (CC BY-SA 3.0).
Credit: @etaubman

This formalizes the exact classification in alex o.'s comment of 2012-05-04:
alpha J - Q is copositive iff every diagonal entry of Q is at most alpha.
The proof below strengthens the source assumption: entrywise nonnegativity
of Q is unnecessary. Positive semidefiniteness alone suffices.
-/

open Matrix
open scoped BigOperators Matrix

namespace OMA.S_mo_95937

def Copositive {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i) → 0 ≤ x ⬝ᵥ (M *ᵥ x)

theorem main : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) (a : ℝ),
    Q.PosSemidef → (∀ i j, 0 ≤ Q i j) →
    (Copositive (fun i j => a - Q i j) ↔ ∀ i, Q i i ≤ a) := by
  sorry

end OMA.S_mo_95937
