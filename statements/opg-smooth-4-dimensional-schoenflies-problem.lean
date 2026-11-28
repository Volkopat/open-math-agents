import Mathlib

/-!
# Smooth 4-dimensional Schoenflies problem

Open Problem Garden: https://www.openproblemgarden.org/op/smooth_4_dimensional_schoenflies_problem
Does every smoothly embedded 3-sphere in 4-space bound a smooth 4-ball?

We state the affirmative answer in `ℝ⁴`: every smooth embedding `f : S³ → ℝ⁴` (smooth,
injective, injective differential; injectivity plus compactness makes it a topological
embedding) is the image of the round unit sphere under a diffeomorphism of `ℝ⁴`. By the
Cerf–Palais disc theorem this is equivalent to the bounded complementary region of the
image being a smooth 4-ball, i.e. to the smooth Schoenflies conjecture.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

open Metric
open scoped Manifold ContDiff

namespace OMA.S_opg_smooth_4_dimensional_schoenflies_problem

instance instFactFinrank : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

/-- Every smoothly embedded `S³ ⊆ ℝ⁴` is ambiently diffeomorphic to the round sphere. -/
theorem main :
    ∀ f : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → EuclideanSpace ℝ (Fin 4),
      ContMDiff (𝓡 3) (𝓡 4) ∞ f →
      Function.Injective f →
      (∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 4) f x)) →
      ∃ Φ : EuclideanSpace ℝ (Fin 4) ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ EuclideanSpace ℝ (Fin 4), Φ '' sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 = Set.range f := by
  sorry

end OMA.S_opg_smooth_4_dimensional_schoenflies_problem
