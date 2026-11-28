import Mathlib

/-!
# An infinite-dimensional Banach space with norm-attaining self-operators

The question asks whether some infinite-dimensional Banach space has the property
that every bounded linear endomorphism attains its norm at a unit vector.

[MathOverflow question](https://mathoverflow.net/questions/232291/do-there-exist-infinite-dimensional-banach-spaces-in-which-every-bounded-linear)
-/

namespace OMA.S_mo_232291

def ExistsSpaceWithNormAttainment (𝕜 : Type) [NontriviallyNormedField 𝕜] : Prop :=
  ∃ (X : Type) (norm : NormedAddCommGroup X),
    letI : NormedAddCommGroup X := norm
    ∃ scalars : NormedSpace 𝕜 X,
      letI : NormedSpace 𝕜 X := scalars
      CompleteSpace X ∧ ¬ FiniteDimensional 𝕜 X ∧
        ∀ T : X →L[𝕜] X, ∃ x : X, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖

theorem main :
    ExistsSpaceWithNormAttainment ℝ ∨ ExistsSpaceWithNormAttainment ℂ := by
  sorry

end OMA.S_mo_232291
