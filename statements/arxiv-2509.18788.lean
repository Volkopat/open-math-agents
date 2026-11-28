import Mathlib

/-!
# The arboreal-gas bunkbed inequality

Source: https://arxiv.org/abs/2509.18788
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

A. Ayyer, S. Linusson and M. Ravichandran, "The bunkbed problem and the random cluster model"
(arXiv:2509.18788). For a finite graph `G = (V, E)`, the bunkbed graph `G̃` has vertices
`v₁, v₂` (`v ∈ V`) and edges `(v₁, v₂)` for `v ∈ V` and `(u_i, v_i)` for `(u, v) ∈ E`, `i ∈ {1, 2}`.
The arboreal gas on a graph `H` with fugacity `λ` is the measure `μ^F_{H,λ}(F) ∝ λ^{|E(F)|}` on
forests `F` of `H`. Conjecture 1.7: for a graph `G` and vertices `u, v` of `G`,
  `μ^F_{G̃,λ}(u₁ ↔ v₁) ≥ μ^F_{G̃,λ}(u₁ ↔ v₂)`.
(The percolation bunkbed conjecture is false (Gladkov–Pak–Zimin), and the paper disproves the
random-cluster version for `0.56 < q < 1.43`; it proves the arboreal version in special cases.)
This file states Conjecture 1.7, for every `λ > 0`.

Modelling choices:
* `G` is a finite simple graph on a finite vertex type `V`; `G̃` is a simple graph on `V × Fin 2`
  (`(v, 0) = v₁`, `(v, 1) = v₂`).
* Forests of `G̃` are edge sets `F ⊆ E(G̃)` whose graph is acyclic. Both probabilities have the same
  normalizing constant `∑_F λ^{|F|}`, so the inequality is stated between the unnormalized sums
  `∑_{F : u₁ ↔ v₁} λ^{|F|}` and `∑_{F : u₁ ↔ v₂} λ^{|F|}`; `x ↔ y` is reachability in `F`.
-/

namespace OMA.S_arxiv_2509_18788

open Classical

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The bunkbed graph `G̃` on `V × Fin 2`: `(v, i) ~ (v, j)` for `i ≠ j` (the posts), and
`(u, i) ~ (v, i)` for `u ~ v` in `G`. (`fromRel` adds `x ≠ y` and symmetrizes; the relation is
already symmetric and loopless.) -/
def bunkbed (G : SimpleGraph V) : SimpleGraph (V × Fin 2) :=
  SimpleGraph.fromRel fun x y => (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ (x.2 = y.2 ∧ G.Adj x.1 y.1)

/-- The (unnormalized) arboreal-gas weight `∑_{F forest of G̃, E(F)} λ^{|F|}` of the event `E`. -/
noncomputable def forestWeight (G : SimpleGraph V) (lam : ℝ)
    (E : Finset (Sym2 (V × Fin 2)) → Prop) : ℝ :=
  ∑ F ∈ (bunkbed G).edgeFinset.powerset,
    if (SimpleGraph.fromEdgeSet (F : Set (Sym2 (V × Fin 2)))).IsAcyclic ∧ E F then
      lam ^ F.card else 0

/-- `x ↔ y` in the forest with edge set `F`. -/
def Conn (F : Finset (Sym2 (V × Fin 2))) (x y : V × Fin 2) : Prop :=
  (SimpleGraph.fromEdgeSet (F : Set (Sym2 (V × Fin 2)))).Reachable x y

/-- **Ayyer–Linusson–Ravichandran, Conjecture 1.7.** -/
theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (lam : ℝ), 0 < lam →
      ∀ u v : V,
        forestWeight G lam (fun F => Conn F (u, 0) (v, 1)) ≤
          forestWeight G lam (fun F => Conn F (u, 0) (v, 0)) := by
  sorry

end OMA.S_arxiv_2509_18788
