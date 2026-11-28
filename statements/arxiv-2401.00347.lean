import Mathlib

/-!
# Structure of betweenness uniform graphs with low values of betweenness centrality

Source: Babak Ghanbari, David Hartman, Vít Jelínek, Aneta Pokorná, Robert Šámal
and Pavel Valtr, arXiv:2401.00347, Conjecture 2 (also Discrete Applied Mathematics,
2026). https://arxiv.org/abs/2401.00347

Conjecture 2. If `G` is a low-betweenness BUG, then its complement is a disjoint
union of stars of the same size.

## Encoding

Betweenness is the paper's unordered sum (§2.1)
`B_G(x) = ∑_{{v,w} ⊆ V(G)} σ_vw(x) / σ_vw`,
where `σ_vw` is the number of shortest `v`–`w` paths and `σ_vw(x)` counts those
on which `x` is internal. Ordered pairs are the other convention, and the paper's
footnote says that convention doubles the value; this file uses unordered pairs.
On `Fin n` each 2-element subset `{v,w}` is the unique pair with `v < w`.

`sigma` and `sigmaThrough` count shortest walks of length `dist` via
`SimpleGraph.finsetWalkLength`. A shortest walk is a path, so this is `σ`.
`[DecidableRel G.Adj]` is the data `finsetWalkLength` needs in order to build
that finite set. Classically every adjacency predicate on `Fin n` is decidable,
so the quantifier runs over every finite simple graph. The cardinalities do not
depend on which decision procedure is chosen.

A BUG is a graph on which every vertex has the same betweenness. A low-betweenness
BUG is a BUG whose common value is strictly less than 1 (§2.1). The paper treats
a disconnected graph as not a BUG: a connected complete multipartite graph on at
least two vertices is uniform but "its complement is disconnected and therefore
not a BUG". Lemma 4 and Theorem 7 are stated for connected graphs, and the
betweenness sum is undefined in ordinary arithmetic when some `σ_vw` is zero.
`LowBUG` therefore requires `G.Connected`. Connectedness makes every denominator
positive. In `ℚ`, division by zero is the junk value `0`; that clause keeps the
junk value out of the statement. The empty vertex set is excluded because
`Connected` requires a vertex.

The conclusion is one common number of leaves `l : ℕ`. A component is the star
`K_{1,l}` when it has `l + 1` vertices, one centre adjacent to all the others,
and no further edge. The paper's construction and Theorem 3 both take `ℓ ≥ 0`,
so `l = 0` is the isolated vertex `K_{1,0}`. Complete graphs are the
betweenness-zero BUGs (diameter 1); their complements are disjoint unions of
isolated vertices, and they are included. "The same size" is a single `l` for
every component, not a separate size for each component. A disjoint union may
have one component or several. No upper bound on `n` or `l` is added.

Graphs are simple, loopless and undirected, as `SimpleGraph`. Every finite
graph of that kind is isomorphic to one with vertex type `Fin n`.

Credit: @mjkang-estrella
-/

namespace OMA.S_arxiv_2401_00347

open scoped BigOperators

variable {n : ℕ}

/-- Number of shortest paths between two vertices (`σ_vw` in the paper). -/
noncomputable def sigma (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) : ℕ := (G.finsetWalkLength (G.dist v w) v w).card

/-- Number of shortest paths between `v` and `w` on which `x` is internal. -/
noncomputable def sigmaThrough (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w x : Fin n) : ℕ :=
  ((G.finsetWalkLength (G.dist v w) v w).filter
    (fun p => x ∈ p.support ∧ x ≠ v ∧ x ≠ w)).card

/-- Unordered betweenness centrality `B_G(x)`. -/
noncomputable def betweenness (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n) : ℚ :=
  ∑ v, ∑ w, if v < w then (sigmaThrough G v w x : ℚ) / sigma G v w else 0

/-- Connected betweenness-uniform graph of common betweenness strictly below 1. -/
def LowBUG (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ (∀ x y, betweenness G x = betweenness G y) ∧
    (∀ x, betweenness G x < 1)

/-- The component is the star `K_{1,l}`: `l` leaves around one centre. -/
def StarComponent (F : SimpleGraph (Fin n)) (l : ℕ) (K : F.ConnectedComponent) : Prop :=
  ∃ c ∈ K.supp, K.supp.ncard = l + 1 ∧
    ∀ u ∈ K.supp, ∀ v ∈ K.supp,
      (F.Adj u v ↔ u ≠ v ∧ (u = c ∨ v = c))

/-- Disjoint union of stars `K_{1,l}`, all with the same number of leaves. -/
def EqualStarUnion (F : SimpleGraph (Fin n)) : Prop :=
  ∃ l : ℕ, ∀ K : F.ConnectedComponent, StarComponent F l K

/-- Conjecture 2: the complement of a low-betweenness BUG is an equal star union. -/
theorem main : ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    LowBUG G → EqualStarUnion Gᶜ := by
  sorry

end OMA.S_arxiv_2401_00347
