import Mathlib

/-!
# The Bermond–Thomassen Conjecture

Source: https://www.openproblemgarden.org/op/the_bermond_thomassen_conjecture
Credit: @lzvxck

The source: for every positive integer `k`, every digraph with minimum out-degree at least
`2k - 1` contains `k` disjoint cycles.

Conventions: digraphs are finite and loopless (`G.Adj v v` never holds); opposite arcs are
allowed, so 2-cycles count as cycles (the source's extremal example, the symmetric complete
digraph on `2k - 1` vertices, relies on them). A (directed) cycle of length `m ≥ 2` is an
injective sequence `c 0, …, c (m-1)` of vertices with an arc from each `c i` to the next one,
cyclically. Disjoint means vertex-disjoint.
-/

namespace OMA.S_opg_the_bermond_thomassen_conjecture

/-- `c : Fin m → V` is a directed cycle of `G`: `m ≥ 2` distinct vertices with an arc from
each to the next, cyclically (`finRotate m` sends `i` to `i + 1 mod m`). -/
def IsDirectedCycle {V : Type*} (G : Digraph V) {m : ℕ} (c : Fin m → V) : Prop :=
  2 ≤ m ∧ Function.Injective c ∧ ∀ i, G.Adj (c i) (c (finRotate m i))

/-- **Bermond–Thomassen conjecture.** For every `k ≥ 1`, every finite loopless digraph with
minimum out-degree at least `2k - 1` contains `k` vertex-disjoint directed cycles. -/
theorem main : ∀ (k : ℕ), 0 < k → ∀ (V : Type) [Fintype V] (G : Digraph V),
    (∀ v, ¬ G.Adj v v) → (∀ v, 2 * k - 1 ≤ {w | G.Adj v w}.ncard) →
      ∃ (m : Fin k → ℕ) (c : (i : Fin k) → Fin (m i) → V),
        (∀ i, IsDirectedCycle G (c i)) ∧
        ∀ i j, i ≠ j → Disjoint (Set.range (c i)) (Set.range (c j)) := by
  sorry

end OMA.S_opg_the_bermond_thomassen_conjecture
