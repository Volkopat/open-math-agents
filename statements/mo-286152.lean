import Mathlib

/-!
# Locally commuting orthogonal projections need not admit commuting replacements

Source: Guest, https://mathoverflow.net/questions/286152 (CC BY-SA 3.0).
Credit: @connoranderson.

Five orthogonal projections on a 25-dimensional complex Hilbert space commute
pairwise on a common line. No five globally commuting idempotents on the same
space can have the specified actions on that line. The obstruction is that the
sum would have eigenvalue 5/2, whereas a sum of commuting idempotents has only
nonnegative integer eigenvalues.
-/
namespace OMA.S_mo_286152
open Finset Submodule
open scoped InnerProductSpace
abbrev Coord := (Fin 3 × Fin 5) ⊕ Fin 10
abbrev H := EuclideanSpace ℂ Coord
abbrev Op := H →L[ℂ] H
theorem main :
    ∃ (u : H) (P : Fin 5 → Op), u≠0 ∧ (∀ i,IsStarProjection (P i)) ∧
      (∀ i j, ∀ y∈ℂ ∙ u,P i (P j y)=P j (P i y)) ∧
      ¬∃ Q : Fin 5 → Op, (∀ i,IsIdempotentElem (Q i)) ∧
        (∀ i, ∀ y∈ℂ ∙ u,Q i y=P i y) ∧ (∀ i j,Commute (Q i) (Q j)) := by
  sorry
end OMA.S_mo_286152
