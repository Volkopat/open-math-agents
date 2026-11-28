import Mathlib

/-!
# Odd-cycle transversal in triangle-free graphs

Source: https://www.openproblemgarden.org/op/odd_cycle_transversal_in_triangle_free_graphs

Conjecture (Erdős). If G is a simple triangle-free graph, then there is a set of at most
n^2/25 edges whose deletion destroys every odd cycle.

Conventions:
* G is a finite simple graph on a vertex type V with n = `Fintype.card V` vertices
  (n is the number of vertices, as usual in this conjecture).
* triangle-free: `G.CliqueFree 3`.
* a set of at most n^2/25 edges: a finite set S of unordered pairs with
  (|S| : ℝ) ≤ n^2 / 25, compared in ℝ so that no rounding is introduced. Pairs that are
  not edges of G change nothing under deletion.
* deletion destroys every odd cycle: every cycle of `G.deleteEdges S` (a closed walk with
  `Walk.IsCycle`) has even length.
-/

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

namespace OMA.S_opg_odd_cycle_transversal_in_triangle_free_graphs

theorem main :
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
      ∃ S : Finset (Sym2 V), (S.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 25 ∧
        ∀ (v : V) (c : (G.deleteEdges (S : Set (Sym2 V))).Walk v v),
          c.IsCycle → Even c.length := by
  sorry

end OMA.S_opg_odd_cycle_transversal_in_triangle_free_graphs
