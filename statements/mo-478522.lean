import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Proving this function is convex

Source: https://mathoverflow.net/questions/478522
Question author: Tom Solberg. Source text is CC BY-SA 4.0.

The claim is convexity of the stated matrix-weighted entropy on the positive
probability simplex, for every symmetric positive definite matrix whose entries
are in [0,1] and whose diagonal entries are one. The transpose convention is real.
-/

namespace OMA.S_mo_478522

def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, x i = 1}

noncomputable def entropy {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i * Real.log (∑ j, C i j * x j)

theorem main :
  ∀ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ),
    C.IsSymm → C.PosDef →
    (∀ i j, 0 ≤ C i j ∧ C i j ≤ 1) → (∀ i, C i i = 1) →
    ConvexOn ℝ (simplex n) (entropy C) := by
  sorry

end OMA.S_mo_478522
