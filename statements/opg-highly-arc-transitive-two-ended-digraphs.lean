import Mathlib

/-!
# Highly arc transitive two ended digraphs

Source: https://www.openproblemgarden.org/op/highly_arc_transitive_two_ended_digraphs
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (DeVos, following McKay–Praeger): if `G` is a highly arc transitive digraph with two
ends, then every tile of `G` is a disjoint union of complete bipartite graphs.

Conventions:
* Digraphs are Mathlib's `Digraph V`, taken connected and locally finite (the setting of
  Cameron–Praeger–Wormald) with ends those of the underlying undirected graph.
* An `s`-arc is a sequence `v₀ → v₁ → ⋯ → v_s`. `G` is highly arc transitive if its automorphism
  group is transitive on `s`-arcs for every `s ≥ 0`.
* Tiles (as in the source): there is a system of imprimitivity `{X_i : i ∈ ℤ}` of finite blocks,
  with every arc going from some `X_i` to `X_{i+1}`; the tile `G[X_i, X_{i+1}]` is the bipartite
  digraph of arcs between consecutive blocks. We encode the blocks by a height `h : V → ℤ` with
  finite fibres and `h w = h u + 1` for every arc `u → w`. In a connected digraph such an `h` is
  unique up to an additive constant, so quantifying over all of them is the same as speaking of
  the source's tiles.
* A bipartite digraph with all arcs from one side to the other is a disjoint union of complete
  bipartite graphs iff `u → w`, `u' → w`, `u → w'` imply `u' → w'`.
-/

namespace OMA.S_opg_highly_arc_transitive_two_ended_digraphs

variable {V : Type}

/-- Automorphisms of a digraph. -/
def IsAut (G : Digraph V) (φ : V ≃ V) : Prop := ∀ u w, G.Adj u w ↔ G.Adj (φ u) (φ w)

/-- `v` is an `s`-arc. -/
def IsArc (G : Digraph V) (s : ℕ) (v : Fin (s + 1) → V) : Prop :=
  ∀ i : Fin s, G.Adj (v i.castSucc) (v i.succ)

/-- Highly arc transitive. -/
def HighlyArcTransitive (G : Digraph V) : Prop :=
  ∀ (s : ℕ) (v w : Fin (s + 1) → V), IsArc G s v → IsArc G s w →
    ∃ φ : V ≃ V, IsAut G φ ∧ ∀ i, φ (v i) = w i

/-- The underlying undirected graph. -/
def underlying (G : Digraph V) : SimpleGraph V := SimpleGraph.fromRel G.Adj

theorem main :
    ∀ (V : Type) (G : Digraph V),
      (underlying G).Connected → (∀ v, {w | G.Adj v w ∨ G.Adj w v}.Finite) →
      HighlyArcTransitive G → Nat.card (underlying G).end = 2 →
      ∀ h : V → ℤ, (∀ i, {v | h v = i}.Finite) → (∀ u w, G.Adj u w → h w = h u + 1) →
        ∀ u u' w w', G.Adj u w → G.Adj u' w → G.Adj u w' → G.Adj u' w' := by
  sorry

end OMA.S_opg_highly_arc_transitive_two_ended_digraphs
