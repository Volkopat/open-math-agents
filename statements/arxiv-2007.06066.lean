import Mathlib

/-!
# Linear arboricity of 2-degenerate graphs of maximum degree 3 or 4

Source: https://arxiv.org/abs/2007.06066 (Basavaraju, Bishnu, Francis, Pattanayak, The linear
arboricity conjecture for graphs of low degeneracy), conjecture of the abstract and Section 1:
χ'_l(G) = ⌈Δ(G)/2⌉ = 2 for every 2-degenerate graph G with Δ(G) ∈ {3, 4}.

A linear forest is an acyclic graph of maximum degree at most 2. A k-linear coloring is an edge
coloring with k colors in which every color class is a linear forest, and the linear arboricity
χ'_l(G) is the least k for which G has a k-linear coloring. A graph is t-degenerate if every
subgraph has a vertex of degree at most t; it suffices to ask this of induced subgraphs on
nonempty vertex sets. Graphs are finite simple graphs on Fin n. Colorings are given on all of
Sym2 (Fin n); only their values on edges of G matter.

Literature: the paper proves the equality for 2-degenerate graphs with Δ ≥ 5 and, for Δ ≤ 4, for
those with at least 2|V| − 5 edges, bipartite ones and those of treewidth at most 2; Chen, Hao
and Yu (arXiv:2207.07169) need Δ ≥ 2k² − k for k-degenerate graphs. No resolution was found.
-/

namespace OMA.S_arxiv_2007_06066

/-- Every nonempty vertex set contains a vertex with at most `t` neighbours inside it. -/
def IsDegenerate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) : Prop :=
  ∀ s : Finset (Fin n), s.Nonempty → ∃ v ∈ s, (s.filter (G.Adj v)).card ≤ t

/-- The edges of `G` with color `i`, as a spanning subgraph. -/
def colorClass {n k : ℕ} (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → Fin k) (i : Fin k) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ c e = i}

/-- `c` is a `k`-linear coloring: every color class is acyclic with maximum degree at most 2. -/
def IsLinearColoring {n k : ℕ} (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → Fin k) : Prop :=
  ∀ i, (colorClass G c i).IsAcyclic ∧ ∀ v, ((colorClass G c i).neighborSet v).ncard ≤ 2

/-- The linear arboricity `χ'_l(G)`. -/
noncomputable def linearArboricity {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ c : Sym2 (Fin n) → Fin k, IsLinearColoring G c}

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    IsDegenerate G 2 → G.maxDegree ∈ ({3, 4} : Finset ℕ) → linearArboricity G = 2 := by
  sorry

end OMA.S_arxiv_2007_06066
