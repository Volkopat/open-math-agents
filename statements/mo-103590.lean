import Mathlib

/-!
# Uniform inverse bounds for finite-dimensional orthogonal compressions

Source: shuhalo, https://mathoverflow.net/questions/103590 (CC BY-SA 3.0).
Credit: @connoranderson.

The source gives an equivalent definition of an upper bound for the norm of
the Moore–Penrose inverse: every vector in the range has a preimage whose
norm is at most the bound times the norm of that vector. For a compression
to G the output is the orthogonal projection of Tx onto G, for x in G.

Over the complex field, a nonzero bounded operator admits a uniform bound C
for all finite-dimensional compressions exactly when its numerical range stays
at distance at least 1/C from zero. Testing lines already forces this
condition. The involution which swaps the coordinates of ℂ² has inverse norm one and arbitrarily ill-conditioned line compressions.
-/
namespace OMA.S_mo_103590
open scoped InnerProductSpace
open Submodule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def liftBound (T : H →L[ℂ] H) (C : ℝ) (G : Submodule ℂ H) [FiniteDimensional ℂ G] : Prop :=
  ∀ x ∈ G, ∃ y ∈ G, G.starProjection (T y) = G.starProjection (T x) ∧
    ‖y‖ ≤ C * ‖G.starProjection (T x)‖

def uniformBound (T : H →L[ℂ] H) (C : ℝ) : Prop :=
  ∀ (G : Submodule ℂ H) [FiniteDimensional ℂ G], liftBound T C G

theorem main :
    (∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      (T : E →L[ℂ] E) (C : ℝ), 0 < C →
       (uniformBound T C ↔ T=0 ∨ ∀ x : E, ‖x‖^2 ≤ C*‖⟪x,T x⟫_ℂ‖)) ∧
    (let E := EuclideanSpace ℂ (Fin 2)
     ∃ T : E ≃ₗᵢ[ℂ] E, Function.Involutive T ∧
       ∀ C : ℝ, 0 < C → ∃ x : E, ‖x‖=1 ∧
         ¬liftBound T.toLinearIsometry.toContinuousLinearMap C (ℂ ∙ x)) := by
  sorry

end OMA.S_mo_103590
