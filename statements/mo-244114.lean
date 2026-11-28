import Mathlib

/-!
# MathOverflow 244114

Source: https://mathoverflow.net/questions/244114
-/

namespace OMA.S_mo_244114

open Polynomial

/-- Fix every variable other than i to its prescribed scalar. -/
noncomputable def specialize {K : Type} [Field K] {n : ℕ} (i : Fin n) (a : Fin n → K) :
    MvPolynomial (Fin n) K →+* K[X] :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = i then Polynomial.X else Polynomial.C (a j))

theorem main : ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ), 2 ≤ n →
    ∀ I : Ideal (MvPolynomial (Fin n) K),
      (∀ (i : Fin n) (a : Fin n → K), (I.map (specialize i a)).IsRadical) → I.IsRadical := by
  sorry

end OMA.S_mo_244114
