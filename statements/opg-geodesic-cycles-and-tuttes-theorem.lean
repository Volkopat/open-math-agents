import Mathlib

/-!
# Geodesic cycles and Tutte's theorem

Source: http://www.openproblemgarden.org/op/geodesic_cycles_and_tuttes_theorem
Credit: @shc261392

Problem (Georgakopoulos and Sprüssel). If `G` is a 3-connected finite graph, is there an
assignment of lengths `ℓ : E(G) → ℝ⁺` to the edges of `G` such that every `ℓ`-geodesic cycle is
peripheral?

A cycle `C` is `ℓ`-geodesic if for every two vertices `x, y` on `C` there is no `x`-`y` path in
`G` shorter, with respect to `ℓ`, than both `x`-`y` arcs on `C`. A cycle is peripheral if it is
induced (has no chord) and its deletion does not disconnect the graph.

Reading used here (the affirmative answer):
* `G` is a finite simple graph; 3-connected means at least 4 vertices, and deleting any at most
  2 vertices leaves a connected graph.
* Lengths are given on unordered pairs, `ℓ : Sym2 V → ℝ`, positive on the edges of `G`; the
  length of a walk is the sum over its edges.
* A cycle is a closed walk `C` with `C.IsCycle`, of length `m`; its vertices are
  `C.getVert 0, …, C.getVert (m - 1)`. For `i < j < m` the two arcs between `C.getVert i` and
  `C.getVert j` have lengths `arc i j` (edges `i, …, j - 1`) and `total - arc i j`. Asking that
  no walk be shorter than both arcs is the same as for paths, since lengths are positive.
* Deleting `C` leaves the subgraph induced on the vertices off `C`, which must be
  preconnected (an empty remainder counts as connected).
-/

namespace OMA.S_opg_geodesic_cycles_and_tuttes_theorem

/-- `G` is 3-connected. -/
def ThreeConnected {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧ ∀ S : Finset V, S.card ≤ 2 → (G.induce {x | x ∉ S}).Connected

/-- Length of the arc of `C` from position `i` to position `j`. -/
def arc {V : Type} {G : SimpleGraph V} (ℓ : Sym2 V → ℝ) {v : V} (C : G.Walk v v) (i j : ℕ) :
    ℝ :=
  ∑ k ∈ Finset.Ico i j, ℓ s(C.getVert k, C.getVert (k + 1))

/-- `C` is `ℓ`-geodesic. -/
def Geodesic {V : Type} {G : SimpleGraph V} (ℓ : Sym2 V → ℝ) {v : V} (C : G.Walk v v) : Prop :=
  ∀ i j : ℕ, i < j → j < C.length → ∀ p : G.Walk (C.getVert i) (C.getVert j),
    min (arc ℓ C i j) (arc ℓ C 0 C.length - arc ℓ C i j) ≤ (p.edges.map ℓ).sum

/-- `C` is peripheral: induced and non-separating. -/
def Peripheral {V : Type} (G : SimpleGraph V) {v : V} (C : G.Walk v v) : Prop :=
  (∀ a ∈ C.support, ∀ b ∈ C.support, G.Adj a b → s(a, b) ∈ C.edges) ∧
    (G.induce {x | x ∉ C.support}).Preconnected

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), ThreeConnected G →
      ∃ ℓ : Sym2 V → ℝ, (∀ e ∈ G.edgeSet, 0 < ℓ e) ∧
        ∀ (v : V) (C : G.Walk v v), C.IsCycle → Geodesic ℓ C → Peripheral G C := by
  sorry

end OMA.S_opg_geodesic_cycles_and_tuttes_theorem
