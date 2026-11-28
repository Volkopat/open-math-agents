import Mathlib

/-!
# An open projection from an embedded closed four-ball

The question asks whether the closed four-ball embeds in the product of the two-sphere
and the real plane with an open first-coordinate projection.

[MathOverflow question](https://mathoverflow.net/questions/54568/open-map-d4-to-s2)
-/

namespace OMA.S_mo_54568

abbrev Disk4 :=
  ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1)

abbrev Sphere2 :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

theorem main :
    ∃ f : Disk4 → Sphere2 × EuclideanSpace ℝ (Fin 2),
      Topology.IsEmbedding f ∧ IsOpenMap (Prod.fst ∘ f) := by
  sorry

end OMA.S_mo_54568
