import OMAStatements.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree
import Mathlib

/-!
Classical slice of Thomassé's conjecture (an oriented graph with minimum outdegree `k` has a
directed path of length `2k`).

H1 is the classical tournament case: if every two distinct vertices are joined by an arc, the
graph is a tournament, it has a Hamiltonian directed path (Rédei, 1934), and counting arcs
(`n k ≤ n (n - 1) / 2`) gives `n ≥ 2k + 1` vertices, so that path has length at least `2k`.
This is a known case, not progress on the conjecture.

H2 is the open rest: oriented graphs with at least one pair of distinct non-adjacent vertices.
-/

namespace OMA.R_opg_directed_cycle_of_length_twice_the_minimum_outdegree_R1

open OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree

/-- Thomassé's conjecture for tournaments. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj] (k : ℕ),
    IsOriented G → (∀ u v, u ≠ v → G.Adj u v ∨ G.Adj v u) →
    (∀ v, k ≤ outdegree G v) → HasDirectedPathOfLength G (2 * k)

/-- Open rest: oriented graphs that are not tournaments. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj] (k : ℕ),
    IsOriented G → (∃ u v, u ≠ v ∧ ¬ G.Adj u v ∧ ¬ G.Adj v u) →
    (∀ v, k ≤ outdegree G v) → HasDirectedPathOfLength G (2 * k)

theorem main : H1 → H2 →
    type_of% @OMA.S_opg_directed_cycle_of_length_twice_the_minimum_outdegree.main := by
  intro h1 h2 V _ _ G _ k hor hk
  by_cases ht : ∀ u v, u ≠ v → G.Adj u v ∨ G.Adj v u
  · exact h1 V G k hor ht hk
  · refine h2 V G k hor ?_ hk
    by_contra hne
    apply ht
    intro u v huv
    by_contra hc
    exact hne ⟨u, v, huv, fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩

end OMA.R_opg_directed_cycle_of_length_twice_the_minimum_outdegree_R1
