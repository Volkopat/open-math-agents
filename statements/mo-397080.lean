import Mathlib

/-!
# A counterexample to a dimension-independent tracial inequality

Source: Lise Wouters, https://mathoverflow.net/questions/397080 (CC BY-SA 4.0).
Credit: @connoranderson.

The source asks whether a uniform bound holds, also offering the weaker
limsup version. Both fail, already for diagonal positive contractions and a
unitary reflection. The eigenvalue functional calculus of a conjugated
diagonal matrix is written in its given eigenbasis. The trace norm includes
the normalization by the dimension. The positive gap persists for arbitrarily
large mesh sizes with the same matrices. The original comments cite Connes,
Annals of Mathematics (1976), Remark 1.2.7 for a related obstruction.
-/

namespace OMA.S_mo_397080
open Matrix
open scoped MatrixOrder ComplexConjugate Matrix.Norms.L2Operator

abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℂ

def ramp (n i : ℕ) (t : ℝ) : ℝ := max 0 (min 1 ((n:ℝ)*t - (i:ℝ)))

noncomputable def sd {k : ℕ} (w a : Fin k → ℝ) : ℝ :=
  Real.sqrt ((∑ i, w i*(a i)^2) - (∑ i, w i*a i)^2)

noncomputable def traceNorm {k : ℕ} (A : Mat k) : ℝ :=
  (Matrix.trace (CFC.sqrt (Aᴴ*A))).re

noncomputable def gap {k : ℕ} (U : Mat k) (a : Fin k → ℝ) : ℝ :=
  let D := Matrix.diagonal (fun j => (a j : ℂ))
  traceNorm (Uᴴ*D*U-D)/(k:ℝ)

theorem main : ∀ C : ℝ, ∃ (k : ℕ) (a : Fin k → ℝ) (U : Mat k),
    0<k ∧ (∀ j, a j ∈ Set.Icc 0 1) ∧ U ∈ Matrix.unitaryGroup (Fin k) ℂ ∧
    ∃ δ : ℝ, 0<δ ∧ ∀ N : ℕ, ∃ n : ℕ, N≤n ∧ 0<n ∧
      C*gap U a + δ ≤ (∑ i : Fin n, gap U (fun j => ramp n i.val (a j)))/(n:ℝ) := by
  sorry

end OMA.S_mo_397080
