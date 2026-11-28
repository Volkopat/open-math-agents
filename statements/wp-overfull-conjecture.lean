import Mathlib

/-!
# Overfull conjecture (Chetwynd–Hilton, 1986)

Source: https://en.wikipedia.org/wiki/Overfull_graph#Overfull_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source statement: a graph `G` with `Δ(G) > n/3` is class 2 if and only if it has an overfull
subgraph `S` such that `Δ(G) = Δ(S)`. Here a graph is overfull if `|E| > Δ · ⌊|V|/2⌋`, and a
graph is class 2 if its chromatic index (edge chromatic number) equals `Δ + 1`.

Conventions:
* `G` is a finite simple graph on `n = Fintype.card V` vertices; `Δ` is Mathlib's `maxDegree`;
* `Δ(G) > n/3` is read over `ℝ`, as in the source (the strict inequality of the source's
  statement box and of Chetwynd–Hilton);
* subgraphs are Mathlib's `G.Subgraph` (not necessarily induced; the source says subgraph).
  For a subgraph `S`, `|V(S)|` is `S.verts.ncard`, `|E(S)|` is `S.edgeSet.ncard`, and `Δ(S)` is the
  maximum degree of `S` viewed as a graph on its own vertex set (`S.coe`);
* the chromatic index is the chromatic number of the line graph (`G.lineGraph.chromaticNumber`,
  a value in `ℕ∞`), and class 2 means it equals `Δ(G) + 1`, as in the source's definition.
-/

namespace OMA.S_wp_overfull_conjecture

open Classical in
/-- Maximum degree of a subgraph, viewed as a simple graph on its own vertex set. -/
noncomputable def subMaxDegree {V : Type} [Fintype V] {G : SimpleGraph V} (S : G.Subgraph) : ℕ :=
  S.coe.maxDegree

/-- `S` is overfull: `|E(S)| > Δ(S) * ⌊|V(S)| / 2⌋`. -/
def IsOverfull {V : Type} [Fintype V] {G : SimpleGraph V} (S : G.Subgraph) : Prop :=
  S.edgeSet.ncard > subMaxDegree S * (S.verts.ncard / 2)

/-- `G` is class 2: its chromatic index (chromatic number of its line graph) is `Δ(G) + 1`. -/
def IsClassTwo {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.lineGraph.chromaticNumber = ((G.maxDegree + 1 : ℕ) : ℕ∞)

theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (G.maxDegree : ℝ) > (Fintype.card V : ℝ) / 3 →
      (IsClassTwo G ↔ ∃ S : G.Subgraph, IsOverfull S ∧ subMaxDegree S = G.maxDegree) := by
  sorry

end OMA.S_wp_overfull_conjecture
