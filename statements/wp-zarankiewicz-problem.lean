import Mathlib

/-!
# Zarankiewicz problem

Source: https://en.wikipedia.org/wiki/Zarankiewicz_problem
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_zarankiewicz_problem

/-!
The source's precise statement formalized here:

* A bipartite graph `G = (U ∪ V, E)` consists of two disjoint sets of vertices `U`, `V`
  and a set of edges each connecting a vertex of `U` to a vertex of `V`; no two edges
  connect the same pair of vertices (a set of pairs).
* `G` contains a subgraph of the form `K_{s,t}` iff there is a set of `s` vertices of `U`
  and `t` vertices of `V` that are all connected to each other. The ordering of `s` and `t`
  is significant: the `s` vertices must be from `U` and the `t` vertices from `V`.
* The Zarankiewicz function `z(m,n;s,t)` denotes the **maximum** possible number of edges
  in a bipartite graph `G = (U ∪ V, E)` with `|U| = m` and `|V| = n` that does not contain
  a subgraph of the form `K_{s,t}`.
* Shorthand: `z(n;t)` is the same as `z(n,n;t,t)`.

The source's "problem" itself — "asks for a formula for the Zarankiewicz function, or
(failing that) for tight asymptotic bounds on the growth rate of `z(n;t)`" — is a request
for a formula/asymptotics, not a proposition with quantifiers; the faithful formalization
of the source's precise content is the defining property of `z(m,n;s,t)` as a maximum,
which `main` states (the maximum exists and is attained).
-/

/-- A bipartite graph with parts `U = Fin m` and `V = Fin n` of sizes `m` and `n`:
a set `E` of edges, each connecting a vertex of `U` to a vertex of `V`. Since `E` is a
set of pairs, no two edges connect the same pair of vertices. -/
abbrev BipartiteGraphEdges (m n : ℕ) : Type := Finset (Fin m × Fin n)

/-- The number of edges of a bipartite graph. -/
def numEdges {m n : ℕ} (E : BipartiteGraphEdges m n) : ℕ := E.card

/-- `E` contains a subgraph of the form `K_{s,t}`: there exists a set of `s` vertices
of `U` and `t` vertices of `V` that are all connected to each other. The ordering of
`s` and `t` is significant: the `s` vertices are from `U` and the `t` vertices from `V`. -/
def HasKST (m n s t : ℕ) (E : BipartiteGraphEdges m n) : Prop :=
  ∃ (A : Finset (Fin m)) (B : Finset (Fin n)),
    A.card = s ∧ B.card = t ∧
    ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ (E : Finset (Fin m × Fin n))

/-- The set of numbers of edges of bipartite graphs `G = (U ∪ V, E)` with `|U| = m`
and `|V| = n` that do not contain a subgraph of the form `K_{s,t}`. -/
def edgeCountsKSTFree (m n s t : ℕ) : Set ℕ :=
  open Classical in
    (Finset.image (numEdges (m := m) (n := n))
      (Finset.filter (fun E => ¬HasKST m n s t E)
        (Finset.univ : Finset (Finset (Fin m × Fin n))) : Finset (Finset (Fin m × Fin n))) :
      Set ℕ)

/-- The Zarankiewicz function `z(m,n;s,t)`: the maximum possible number of edges in a
bipartite graph `G = (U ∪ V, E)` with `|U| = m` and `|V| = n` that does not contain a
subgraph of the form `K_{s,t}`. -/
noncomputable def zarankiewiczZ (m n s t : ℕ) : ℕ := sSup (edgeCountsKSTFree m n s t)

/-- Shorthand for an important special case: `z(n;t)` is the same as `z(n,n;t,t)`. -/
noncomputable abbrev zarankiewiczZ' (n t : ℕ) : ℕ := zarankiewiczZ n n t t

/-- (Zarankiewicz, 1951) The Zarankiewicz function `z(m,n;s,t)` is the maximum possible
number of edges of a bipartite graph with `|U| = m` and `|V| = n` containing no
subgraph of the form `K_{s,t}`: the value is attained by some `K_{s,t}`-free bipartite
graph, and no `K_{s,t}`-free bipartite graph has more edges. -/
theorem main :
    ∀ m n s t : ℕ,
      (∃ E : BipartiteGraphEdges m n,
          ¬HasKST m n s t E ∧ numEdges E = zarankiewiczZ m n s t) ∧
        (∀ E : BipartiteGraphEdges m n,
            ¬HasKST m n s t E → numEdges E ≤ zarankiewiczZ m n s t) := by
  sorry

end OMA.S_wp_zarankiewicz_problem
