import Mathlib

/-!
# Lower-Hölder embeddings of the sphere

Source: Pablo Shmerkin, https://mathoverflow.net/questions/153842
Credit: @wtho704

The sphere carries the distance inherited from the ambient Euclidean space,
so the lower bound compares chord distances.
-/

namespace OMA.S_mo_153842

theorem main :
    ∀ d : ℕ, 3 ≤ d →
      ∃ (s r : ℝ) (f : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
          EuclideanSpace ℝ (Fin d)),
        0 < s ∧ s < 1 ∧ 0 < r ∧ Topology.IsEmbedding f ∧
          ∀ x y, dist x y < r → dist x y ^ s ≤ dist (f x) (f y) := by
  sorry

end OMA.S_mo_153842
