import Mathlib

/-!
# When is a compact topological 4-manifold a CW complex?

Source: https://mathoverflow.net/questions/73428
When is a compact topological 4-manifold (homeomorphic to) a CW complex? Smoothable ones
are (they have handle decompositions), while Freedman's `E₈`-manifold is not triangulable.
The question is open even in the strongest form, and `main` states the affirmative answer
in that form: every compact topological 4-manifold is homeomorphic to a CW complex.

Conventions. A compact topological 4-manifold is a compact Hausdorff space with a
`ChartedSpace (EuclideanSpace ℝ (Fin 4))` structure (closed manifold). CW complexes are
Mathlib's `Topology.CWComplex`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_73428

theorem main :
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M],
      ∃ (X : Type) (_ : TopologicalSpace X) (C : Set X) (_ : Topology.CWComplex C),
        Nonempty (M ≃ₜ C) := by
  sorry

end OMA.S_mo_73428
