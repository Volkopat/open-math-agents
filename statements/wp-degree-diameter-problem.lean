import Mathlib

/-!
# Degree diameter problem

Source: https://en.wikipedia.org/wiki/Degree_diameter_problem
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_degree_diameter_problem

open SimpleGraph

/--
The source (lead section): "Given positive integers `d` and `k`, what is the maximum
possible number of vertices in a finite simple graph of maximum degree at most `d`
and diameter at most `k`?"

`vertexCounts d k` is the set `{ |V(G)| : Δ(G) ≤ d, diam(G) ≤ k }` from the source's
definition of `n_{d,k}`, ranging over finite simple graphs `G`:
* finite simple graph: a `SimpleGraph` on a `Fintype` vertex type;
* `Δ(G) ≤ d`: every vertex has degree at most `d` (the neighbor set of every
  vertex has cardinality `Set.ncard (G.neighborSet v) ≤ d`; the neighbor sets are
  finite since `V` is);
* `diam(G) ≤ k`: the extended diameter `G.ediam` (which is `⊤` for disconnected
  graphs, so the bound forces connectedness, as in the source's convention) is at
  most `(k : ℕ∞)`.
-/
def vertexCounts (d k : ℕ) : Set ℕ :=
  { c | ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = c ∧ (∀ v, Set.ncard (G.neighborSet v) ≤ d) ∧ G.ediam ≤ (k : ℕ∞) }

/-- `n_{d,k}` in the source: the maximum number of vertices of a finite simple graph
of maximum degree at most `d` and diameter at most `k`. -/
noncomputable def n (d k : ℕ) : ℕ :=
  sSup (vertexCounts d k)

/--
Degree–diameter problem (source statement, exactly as stated): for positive integers
`d` and `k`, the source defines `n_{d,k} = max { |V(G)| : Δ(G) ≤ d, diam(G) ≤ k }`.
The `max` asserts the maximum is attained: there is a finite simple graph of maximum
degree at most `d` and diameter at most `k` with `n d k` vertices.
-/
theorem main :
    ∀ (d k : ℕ), 0 < d → 0 < k →
      ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
        Fintype.card V = n d k ∧ (∀ v, Set.ncard (G.neighborSet v) ≤ d) ∧ G.ediam ≤ (k : ℕ∞) := by
  sorry

end OMA.S_wp_degree_diameter_problem
