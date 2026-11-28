import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Rat.Lemmas

/-!
# Sharpness of the bivariate polynomial divisibility threshold

Source: https://mathoverflow.net/questions/332685
Credit: @Spinausore

Maxim Nikitin asks whether the local divisibilities in Spielman's lemma can
hold without global divisibility when the degree ratio reaches or exceeds 1.
We state the sharpness assertion at equality. The two degrees of P, divided
by the respective grid sizes, sum to 1. The four real parameters in the source
can be recovered from the degrees: α and β are the normalized degrees of E,
and δ and ε are the normalized gaps between the degrees of P and E.
-/

namespace OMA.S_mo_332685

open Polynomial

/-- A bivariate polynomial is an outer polynomial in Y with coefficients in K[X]. -/
abbrev Biv (K : Type) [Semiring K] := Polynomial (Polynomial K)

noncomputable def atX {K : Type} [Field K] (a : K) (p : Biv K) : Polynomial K :=
  p.map (evalRingHom a)

noncomputable def atY {K : Type} [Field K] (b : K) (p : Biv K) : Polynomial K :=
  p.eval (C b)

/-- Interchanging X and Y makes the X degree the ordinary outer degree. -/
noncomputable def swap {K : Type} [Field K] (p : Biv K) : Biv K :=
  eval₂RingHom (mapRingHom (C : K →+* Polynomial K)) (C X) p

noncomputable def degreeX {K : Type} [Field K] (p : Biv K) : ℕ :=
  (swap p).natDegree

/-- Local divisibility does not force global divisibility at the boundary 1. -/
theorem main :
    ∃ (K : Type) (_ : Field K) (m n : ℕ) (x : Fin m → K) (y : Fin n → K)
      (E P : Biv K),
      0 < m ∧ 0 < n ∧ Function.Injective x ∧ Function.Injective y ∧
      E ≠ 0 ∧ P ≠ 0 ∧ degreeX E ≤ degreeX P ∧ E.natDegree ≤ P.natDegree ∧
      degreeX P * n + P.natDegree * m = m * n ∧
      (∀ i, atX (x i) E ∣ atX (x i) P) ∧
      (∀ j, atY (y j) E ∣ atY (y j) P) ∧ ¬ E ∣ P := by
  sorry

end OMA.S_mo_332685
