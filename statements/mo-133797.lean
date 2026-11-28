import Mathlib

/-!
# Existence of an exotic smooth four-torus

The question asks whether some smooth four-manifold is homeomorphic to the standard
four-torus while admitting no smooth diffeomorphism to it.

[MathOverflow question](https://mathoverflow.net/questions/133797/do-there-exist-exotic-4-tori)
-/

open scoped Manifold ContDiff

namespace OMA.S_mo_133797

abbrev Torus4 := Circle × Circle × Circle × Circle

noncomputable abbrev TorusModel := (𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))

theorem main :
    ∃ (M : Type) (topology : TopologicalSpace M),
      letI : TopologicalSpace M := topology
      ∃ charts : ChartedSpace
          (ModelProd (EuclideanSpace ℝ (Fin 1))
            (ModelProd (EuclideanSpace ℝ (Fin 1))
              (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))))) M,
        letI : _ := charts
        IsManifold TorusModel ∞ M ∧
          Nonempty (M ≃ₜ Torus4) ∧
          ¬ Nonempty (Diffeomorph TorusModel TorusModel M Torus4 ∞) := by
  sorry

end OMA.S_mo_133797
