import Mathlib

/-!
# Does a hereditary 2-coloring imply a polychromatic 3-coloring for large edges?

Source: https://mathoverflow.net/questions/332985 (Dömötör Pálvölgyi)
Credit: @jagraj28

For a hypergraph `H = (V, E)`, `m_k(H)` is the smallest `m` such that every `X ⊆ V` can be
`k`-colored so that every edge `e` with `|e ∩ X| ≥ m` sees all `k` colors in `e ∩ X`. Berge
proved that `m_2 = 2` holds exactly when every odd cycle has an edge containing three vertices of
the cycle, and that then `m_k = k` for all `k`. The question:

  Does `m_2 = 3` imply any upper bound on `m_3`?

It has no answer. Pálvölgyi (arXiv:2309.04603) gave a 5-uniform hypergraph with `m_2 = 3` and
`m_3 = 6`, disproving the guess `m_3 ≤ 5`; a 2026 follow-up (arXiv:2604.24412) extends the
construction to larger uniformities, which does not settle the question.

`main` states a positive answer: there is a constant `C` such that every finite hypergraph with
`m_2 ≤ 3` has `m_3 ≤ C`. A proof of `¬ main` would give finite hypergraphs with `m_2 ≤ 3` and
`m_3` arbitrarily large.

Conventions.
* Hypergraphs are finite: a finite vertex type `V` and a finite set `E` of edges, each a
  `Finset V`. For a finite hypergraph `m_k` is always finite, so "an upper bound" means a bound
  that does not depend on the hypergraph.
* `HasPolychromatic k m E` says `m_k ≤ m`: for every `X : Finset V` there is a coloring
  `c : V → Fin k` such that every edge `e ∈ E` with `m ≤ |e ∩ X|` contains, for each color `i`,
  a vertex of `e ∩ X` of color `i`. (Only the colors of vertices in `X` matter.)
* The hypothesis is `m_2 ≤ 3` rather than `m_2 = 3`; this is the same question, since `m_2 ≤ 2`
  already gives `m_3 = 3` by Berge's theorem.
-/

namespace OMA.S_mo_332985

/-- `m_k(E) ≤ m`: every vertex subset `X` has a `k`-coloring in which every edge meeting `X` in
at least `m` vertices sees all `k` colors inside `X`. -/
def HasPolychromatic {V : Type} [DecidableEq V] (k m : ℕ) (E : Finset (Finset V)) : Prop :=
  ∀ X : Finset V, ∃ c : V → Fin k, ∀ e ∈ E, m ≤ (e ∩ X).card →
    ∀ i : Fin k, ∃ v ∈ e ∩ X, c v = i

/-- A positive answer: `m_2 ≤ 3` implies a uniform upper bound on `m_3`. -/
theorem main : ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (E : Finset (Finset V)),
    HasPolychromatic 2 3 E → HasPolychromatic 3 C E := by
  sorry

end OMA.S_mo_332985
