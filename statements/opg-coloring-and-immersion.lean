import Mathlib

/-!
# Coloring and immersion

Source: https://www.openproblemgarden.org/op/coloring_and_immersion
Credit: @shc261392

Conjecture (Abu-Khzam and Langston): for every positive integer `t`, every (loopless) graph `G`
with `χ(G) ≥ t` immerses `K_t`.

`G` immerses `H` if a graph isomorphic to `H` can be obtained from `G` by repeatedly splitting
off pairs of adjacent edges and deleting vertices and edges. Equivalently, there is an injective
map `φ` from `V(H)` to `V(G)` and, for each edge `xy` of `H`, a path in `G` from `φ x` to `φ y`,
these paths being pairwise edge-disjoint (they may pass through vertices of `φ(V(H))`).

Reading used here:
* `G` is a finite simple graph. This loses nothing: deleting parallel edges does not change the
  chromatic number, and an immersion in the resulting simple graph is an immersion in `G`.
* An immersion of `K_t` is an injective `φ : Fin t → V` together with paths `P i j` from `φ i`
  to `φ j` for `i < j`, pairwise edge-disjoint.
-/

namespace OMA.S_opg_coloring_and_immersion

/-- `G` immerses the complete graph `K_t`. -/
def ImmersesComplete {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ φ : Fin t → V, Function.Injective φ ∧
    ∃ P : ∀ i j : Fin t, G.Walk (φ i) (φ j),
      (∀ i j, i < j → (P i j).IsPath) ∧
      ∀ i j i' j', i < j → i' < j' → (i, j) ≠ (i', j') → (P i j).edges.Disjoint (P i' j').edges

theorem main :
    ∀ (t : ℕ), 1 ≤ t → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (t : ℕ∞) ≤ G.chromaticNumber → ImmersesComplete G t := by
  sorry

end OMA.S_opg_coloring_and_immersion
