import Mathlib

/-!
# A Nordhaus–Gaddum conjecture for the minimum number of distinct eigenvalues

Source: https://arxiv.org/abs/1807.06436 (Levene, Oblak, Šmigoc), Conjecture 1.2: for any graph
G, the inequality q(G) + q(Gᶜ) ≤ |G| + 2 holds if and only if G is not one of the four graphs
P₄, P₅, P₅ᶜ and T₂,₂.

S(G) is the set of real symmetric n × n matrices whose off-diagonal entry (i, j) is nonzero exactly
when ij is an edge of G (diagonal unrestricted), and q(G) is the minimum number of distinct
eigenvalues of a matrix in S(G). Since such matrices are real symmetric, their distinct
eigenvalues are the distinct real roots of the characteristic polynomial. T₂,₂ is P₅ with the extra
edge between its second and fourth vertices (a triangle with a pendant vertex at two corners).
Graphs are on the vertex set Fin n.

Literature: the paper verifies the conjecture for trees, unicyclic graphs, graphs with q(G) ≤ 4 and
graphs on at most 7 vertices; no proof or counterexample was found in later work.
-/

namespace OMA.S_arxiv_1807_06436

open SimpleGraph

/-- The matrices of `S(G)`: real symmetric, off-diagonal support exactly the edges of `G`. -/
def S {n : ℕ} (G : SimpleGraph (Fin n)) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | A.IsSymm ∧ ∀ i j, i ≠ j → (A i j ≠ 0 ↔ G.Adj i j)}

/-- `q(G)`: the minimum number of distinct eigenvalues of a matrix in `S(G)`. -/
noncomputable def q {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ A ∈ S G, A.charpoly.roots.toFinset.card = k}

/-- `T₂,₂`: the path on five vertices with the extra edge between its second and fourth vertices. -/
def T22 : SimpleGraph (Fin 5) := pathGraph 5 ⊔ SimpleGraph.edge 1 3

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    q G + q Gᶜ ≤ n + 2 ↔
      ¬ (Nonempty (G ≃g pathGraph 4) ∨ Nonempty (G ≃g pathGraph 5) ∨
        Nonempty (G ≃g (pathGraph 5)ᶜ) ∨ Nonempty (G ≃g T22)) := by
  sorry

end OMA.S_arxiv_1807_06436
