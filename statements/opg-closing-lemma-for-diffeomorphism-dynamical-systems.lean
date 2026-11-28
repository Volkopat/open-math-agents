import Mathlib

/-!
# The closing lemma in the Cʳ topology

Given a nonwandering point of a Cʳ diffeomorphism of a closed smooth manifold,
every Cʳ neighborhood is conjectured to contain a diffeomorphism for which the
same point is periodic.

[Open Problem Garden](https://www.openproblemgarden.org/op/closing_lemma_for_diffeomorphism_dynamical_systems)
[Pugh and Robinson](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0143385700001978)
-/

open scoped ContDiff Manifold Topology

namespace OMA.S_opg_closing_lemma_for_diffeomorphism_dynamical_systems

abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

def IsNonwandering {M : Type} [TopologicalSpace M] (f : M → M) (p : M) : Prop :=
  ∀ U : Set M, U ∈ 𝓝 p →
    ∃ n : ℕ, 0 < n ∧ (U ∩ (f^[n]) ⁻¹' U).Nonempty

def FitsCharts {M : Type} [TopologicalSpace M] (d : ℕ)
    [ChartedSpace (Euclidean d) M] (f : M → M) (x y : M) (K : Set (Euclidean d)) : Prop :=
  K ⊆ (chartAt (Euclidean d) x).target ∧
    Set.MapsTo (f ∘ (chartAt (Euclidean d) x).symm) K (chartAt (Euclidean d) y).source

noncomputable def inCharts {M : Type} [TopologicalSpace M] (d : ℕ)
    [ChartedSpace (Euclidean d) M] (f : M → M) (x y : M) : Euclidean d → Euclidean d :=
  chartAt (Euclidean d) y ∘ f ∘ (chartAt (Euclidean d) x).symm

theorem main :
    ∀ (d : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [ChartedSpace (Euclidean d) M] [IsManifold (𝓡 d) ∞ M] [CompactSpace M],
      ∀ r : ℕ∞, 1 ≤ r →
        ∀ (f : Diffeomorph (𝓡 d) (𝓡 d) M M r) (p : M), IsNonwandering f p →
          ∀ (order patches : ℕ), (order : ℕ∞) ≤ r →
            ∀ (sourceCenter targetCenter : Fin patches → M)
              (K : Fin patches → Set (Euclidean d)),
              (∀ i, IsCompact (K i) ∧ FitsCharts d f (sourceCenter i) (targetCenter i) (K i)) →
                ∀ ε : ℝ, 0 < ε →
                  ∃ g : Diffeomorph (𝓡 d) (𝓡 d) M M r,
                    (∃ n : ℕ, 0 < n ∧ ((g : M → M)^[n]) p = p) ∧
                    ∀ i, FitsCharts d g (sourceCenter i) (targetCenter i) (K i) ∧
                      ∀ l ≤ order, ∀ z ∈ K i,
                        ‖iteratedFDeriv ℝ l (inCharts d g (sourceCenter i) (targetCenter i)) z -
                          iteratedFDeriv ℝ l (inCharts d f (sourceCenter i) (targetCenter i)) z‖ <
                          ε := by
  sorry

end OMA.S_opg_closing_lemma_for_diffeomorphism_dynamical_systems
