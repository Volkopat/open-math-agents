import Mathlib

/-!
# Short directed cycles in bipartite digraphs

Source: https://arxiv.org/abs/1809.08324, Conjecture 1.5
(Paul Seymour and Sophie Spirkl)
Credit: @pyaf

Conjecture: for every integer k ≥ 1 and all reals α, β > 0 with kα + β > 1,
if G is a non-null bipartite digraph with bipartition (A, B), where every
vertex in A has out-degree at least β|B| and every vertex in B has
out-degree at least α|A|, then G has a directed cycle of length at most 2k.
The paper proves it for k = 1, 2. It implies the Caccetta–Häggkvist
conjecture. Searches of arXiv for later work on bipartite digraphs and
Caccetta–Häggkvist found no resolution.

Digraphs have no loops or parallel edges, but uv and vu may both be edges.
Every edge of a bipartite digraph goes from A to B (relation r) or from B to
A (relation s). Both parts are taken nonempty: with B empty the degree
conditions hold trivially in an edgeless digraph. A closed directed walk of
length at most 2k contains a directed cycle of length at most 2k, so the
conclusion asks for such a closed walk a₀ b₀ a₁ b₁ ⋯ a_(j-1) b_(j-1) a₀.
-/

namespace OMA.S_arxiv_1809_08324

theorem main : ∀ (k : ℕ), 1 ≤ k → ∀ α β : ℝ, 0 < α → 0 < β → 1 < k * α + β →
    ∀ (A B : Type) [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
      (r : A → B → Prop) (s : B → A → Prop) [∀ a, DecidablePred (r a)]
      [∀ b, DecidablePred (s b)],
      (∀ a, β * Fintype.card B ≤ (Finset.univ.filter (r a)).card) →
      (∀ b, α * Fintype.card A ≤ (Finset.univ.filter (s b)).card) →
      ∃ j, 1 ≤ j ∧ j ≤ k ∧ ∃ (a : ℕ → A) (b : ℕ → B), a j = a 0 ∧
        ∀ i < j, r (a i) (b i) ∧ s (b i) (a (i + 1)) := by
  sorry

end OMA.S_arxiv_1809_08324
