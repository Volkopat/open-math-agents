import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Ring.Parity

/-!
# Goldberg–Seymour conjecture

Source: https://en.wikipedia.org/wiki/Goldberg%E2%80%93Seymour_conjecture

For every finite loopless multigraph `G`, the chromatic index `χ'(G)` satisfies
`χ'(G) ≤ max (Δ(G) + 1) Γ(G)`, where `Δ(G)` is the maximum vertex degree of `G` and
`Γ(G) = max { ⌈2 |E(G[S])| / (|S| - 1)⌉ | S ⊆ V(G), |S| ≥ 3, |S| odd }` is the fractional
edge-coloring density over odd vertex subsets of size at least 3.

Equivalently, any natural number `k` satisfying `deg(x) + 1 ≤ k` for every vertex `x` and
`2 * |E(G[S])| ≤ k * (|S| - 1)` for every odd subset `S` with `|S| ≥ 3` suffices for a proper
`k`-edge-coloring of `G`.
-/

namespace OMA.S_wp_goldberg_seymour_conjecture

/-- A finite loopless multigraph with `numVertices` vertices and `numEdges` undirected edges. -/
structure LooplessMultigraph where
  numVertices : ℕ
  numEdges : ℕ
  u : Fin numEdges → Fin numVertices
  v : Fin numEdges → Fin numVertices
  loopless : ∀ e : Fin numEdges, u e ≠ v e

/-- Vertex `x` is incident to edge `e`. -/
def LooplessMultigraph.incident (G : LooplessMultigraph)
    (x : Fin G.numVertices) (e : Fin G.numEdges) : Prop :=
  G.u e = x ∨ G.v e = x

/-- The degree of vertex `x` in `G` (each incident loopless edge counts once). -/
def LooplessMultigraph.deg (G : LooplessMultigraph) (x : Fin G.numVertices) : ℕ :=
  ((Finset.univ : Finset (Fin G.numEdges)).filter (fun e => G.u e = x ∨ G.v e = x)).card

/-- The number of edges of `G` with both endpoints in `S`. -/
def LooplessMultigraph.inducedEdgeCount (G : LooplessMultigraph)
    (S : Finset (Fin G.numVertices)) : ℕ :=
  ((Finset.univ : Finset (Fin G.numEdges)).filter (fun e => G.u e ∈ S ∧ G.v e ∈ S)).card

/-- `G` admits a proper `k`-edge-coloring: distinct edges sharing a vertex get distinct colors. -/
def LooplessMultigraph.HasProperEdgeColoring (G : LooplessMultigraph) (k : ℕ) : Prop :=
  ∃ c : Fin G.numEdges → Fin k,
    ∀ x : Fin G.numVertices, ∀ e₁ e₂ : Fin G.numEdges,
      G.incident x e₁ → G.incident x e₂ → e₁ ≠ e₂ → c e₁ ≠ c e₂

theorem main :
    ∀ (G : LooplessMultigraph) (k : ℕ),
      (∀ x : Fin G.numVertices, G.deg x + 1 ≤ k) →
      (∀ S : Finset (Fin G.numVertices),
        3 ≤ S.card → Odd S.card → 2 * G.inducedEdgeCount S ≤ k * (S.card - 1)) →
      G.HasProperEdgeColoring k := by
  sorry

end OMA.S_wp_goldberg_seymour_conjecture
