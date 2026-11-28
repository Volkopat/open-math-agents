import Mathlib

/-!
# Jorgensen's Conjecture

Source: https://www.openproblemgarden.org/op/jorgensens_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture: every 6-connected graph without a `K_6` minor is apex (planar plus one vertex).

Conventions (graphs are finite and simple).
* `k`-connected: more than `k` vertices, and deleting any fewer than `k` vertices leaves a
  connected graph.
* `K_6` minor: six nonempty, pairwise disjoint vertex sets, each inducing a connected
  subgraph, with an edge between every two of them.
* Planar: the graph has a drawing in the plane with vertices at distinct points and edges as
  arcs (continuous injective images of `[0,1]`) joining their endpoints, no arc passing
  through another vertex, and two arcs meeting only at common endpoints.
* Apex: some vertex `v` has `G - v` planar.
-/

namespace OMA.S_opg_jorgensens_conjecture

open SimpleGraph

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `G` is planar: it has a crossing-free drawing in the plane with arcs as edges. -/
def IsPlanar {W : Type*} (G : SimpleGraph W) : Prop :=
  ∃ (pos : W → Plane) (arc : W → W → unitInterval → Plane),
    Function.Injective pos ∧
    (∀ u v, G.Adj u v →
      Continuous (arc u v) ∧ Function.Injective (arc u v) ∧
      arc u v 0 = pos u ∧ arc u v 1 = pos v ∧
      ∀ w, pos w ∈ Set.range (arc u v) → w = u ∨ w = v) ∧
    ∀ u v u' v', G.Adj u v → G.Adj u' v' → s(u, v) ≠ s(u', v') →
      Set.range (arc u v) ∩ Set.range (arc u' v') ⊆ pos '' ({u, v} ∩ {u', v'})

/-- `G` is `k`-connected. -/
def IsKConnected {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce {v | v ∉ S}).Connected

/-- `G` has a `K_6` minor. -/
def HasK6Minor {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ B : Fin 6 → Set V,
    (∀ i, (B i).Nonempty) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, (G.induce (B i)).Connected) ∧
    ∀ i j, i ≠ j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y

/-- `G` is apex: deleting some vertex leaves a planar graph. -/
def IsApex {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ v : V, IsPlanar (G.induce {w | w ≠ v})

/-- Jorgensen's conjecture. -/
theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      IsKConnected G 6 → ¬ HasK6Minor G → IsApex G := by
  sorry

end OMA.S_opg_jorgensens_conjecture
