import Mathlib

/-!
# A strengthened Murty–Simon bound for non-bipartite diameter-2-critical graphs

Source: https://arxiv.org/abs/1812.08420, Conjecture 3 (bound part, as in the
abstract) (Antoine Dailly, Florent Foucaud and Adriana Hansberg)
Credit: @pyaf

A graph is diameter-2-critical (D2C) if its diameter is 2 but deleting any edge
increases the diameter. Conjecture 3: if G is a non-bipartite D2C graph of
order n other than the graph H₅ of Figure 2, then G has at most
⌊(n − 1)²/4⌋ + 1 edges. (The conjecture also lists the extremal graphs: the
family C₅⁺ and thirteen graphs drawn in Figure 3; that characterization is
not stated here.) Bipartite D2C graphs are the complete bipartite graphs.

H₅ has six vertices and eight edges. A computer search over all graphs on at
most 7 vertices finds that it is the only non-bipartite D2C graph there above
the bound, which fixes it up to isomorphism as the graph below.

Later work: arXiv:2610.39032 proves the Murty–Simon bound ⌊n²/4⌋ for all n
and cites this paper only for stronger bounds on restricted classes; Lin and
Wang (Discrete Appl. Math. 2025) treat the C₅-free case. Searches of arXiv
for diameter-2-critical graphs found no proof of this bound.
-/

namespace OMA.S_arxiv_1812_08420

open SimpleGraph

/-- Diameter 2, and deleting any edge increases the diameter (as in
formal-conjectures, Erdős Problem 742). -/
def IsDiameter2Critical {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2

/-- The graph H₅: triangles 0-1-2 and 0-3-4 sharing vertex 0, and a vertex 5
adjacent to 1 and 3. -/
def H5 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet
    {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 5), s(3, 4), s(3, 5)}

theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsDiameter2Critical G → ¬ G.IsBipartite → IsEmpty (G ≃g H5) →
    G.edgeFinset.card ≤ (Fintype.card V - 1) ^ 2 / 4 + 1 := by
  sorry

end OMA.S_arxiv_1812_08420
