import Mathlib

/-!
# Saturation in the Hypercube

Source: https://www.openproblemgarden.org/op/saturation_in_the_hypercube
Credit: @pyaf

Let `G` and `H` be graphs. A spanning subgraph `F` of `G` is `(G,H)`-saturated if `F` contains
no copy of `H` but `F + e` contains a copy of `H` for every edge `e ∈ E(G) \ E(F)`. Let
`sat(G,H)` be the minimum number of edges in a `(G,H)`-saturated graph, and let `Q_d` be the
`d`-dimensional hypercube.

Question (Morrison, Noel and Scott): For fixed `m ≥ 2`, is it true that `sat(Q_d,Q_m) / 2^d`
converges as `d → ∞`?

Formalization notes:
- The source page also asks two open-ended questions (determine `sat(Q_d, C_{2ℓ})`, and improve
  the bounds on `sat(Q_d,Q_m)`). Only the yes/no question above is stated; `main` asserts the
  affirmative answer, and a disproof refutes it.
- `Q_d` has vertex set `Fin d → Bool`, two vertices adjacent when they differ in exactly one
  coordinate (Hamming distance 1).
- A copy of `H` in `F` is a subgraph of `F` isomorphic to `H`: Mathlib's `IsContained H F`.
- A spanning subgraph of `G` is a `F : SimpleGraph V` with `F ≤ G`; adding the edge `uv` is
  `F ⊔ SimpleGraph.edge u v`. The number of edges is `F.edgeSet.ncard`.
- `sat` is the infimum over the (finite, nonempty for `d ≥ m`, since a maximal `Q_m`-free
  spanning subgraph is saturated) set of edge counts of saturated graphs.
-/

namespace OMA.S_opg_saturation_in_the_hypercube

open Filter
open scoped Topology

/-- The `d`-dimensional hypercube `Q_d`. -/
def hypercube (d : ℕ) : SimpleGraph (Fin d → Bool) :=
  SimpleGraph.fromRel fun x y => hammingDist x y = 1

/-- `F` is a `(G,H)`-saturated spanning subgraph of `G`. -/
def IsSaturated {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (F : SimpleGraph V) : Prop :=
  F ≤ G ∧ ¬ H.IsContained F ∧
    ∀ u v, G.Adj u v → ¬ F.Adj u v → H.IsContained (F ⊔ SimpleGraph.edge u v)

/-- `sat(G,H)`: the minimum number of edges of a `(G,H)`-saturated graph. -/
noncomputable def sat {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : ℕ :=
  sInf {k | ∃ F : SimpleGraph V, IsSaturated G H F ∧ F.edgeSet.ncard = k}

theorem main : ∀ m : ℕ, 2 ≤ m → ∃ L : ℝ,
    Tendsto (fun d : ℕ => (sat (hypercube d) (hypercube m) : ℝ) / 2 ^ d) atTop (𝓝 L) := by
  sorry

end OMA.S_opg_saturation_in_the_hypercube
