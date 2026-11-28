import Mathlib

/-!
# Are there any snarks with the following property?

Source: https://mathoverflow.net/questions/497434
Credit: @zarnab222-dev

The question fixes its own meaning of snark: a 3-connected cubic graph whose edges have no
3-colouring (no girth or cyclic-connectivity condition). It asks whether there is such a graph G
with a cycle C that has no chords and such that V(G) - V(C) is an independent set. The affirmative
answer is stated; the optional parity condition on |V(C)|/3 is not imposed, as in the main question.

Translation choices.
* Graphs are finite simple graphs on `Fin n`; a finite graph is one on `Fin n` up to isomorphism.
* Cubic: every vertex has exactly three neighbours (`Set.ncard` of the neighbour set is 3).
* 3-connected is vertex connectivity in the textbook sense (Diestel): more than 3 vertices, and
  deleting any set of fewer than 3 vertices (the empty set included) leaves a connected graph.
  For cubic graphs this agrees with 3-edge-connectivity.
* No 3-colouring of the edges: there is no map from edges to 3 colours giving different colours to
  any two distinct edges of G with a common endpoint. The map is defined on all of `Sym2 (Fin n)`,
  only its values on edges of G are constrained.
* The cycle is a Mathlib closed walk with `IsCycle` (no repeated edge, no repeated vertex except
  the endpoint, so length at least 3). No chords: any edge of G joining two vertices of C is an
  edge of C. Independent complement: no edge of G joins two vertices outside C.
-/

namespace OMA.S_mo_497434

theorem main : ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ v : Fin n, (G.neighborSet v).ncard = 3) ∧
    (3 < n ∧ ∀ S : Finset (Fin n), S.card < 3 → (G.induce {v | v ∉ S}).Connected) ∧
    (¬ ∃ c : Sym2 (Fin n) → Fin 3, ∀ e₁ ∈ G.edgeSet, ∀ e₂ ∈ G.edgeSet,
        e₁ ≠ e₂ → (∃ v, v ∈ e₁ ∧ v ∈ e₂) → c e₁ ≠ c e₂) ∧
    (∃ (u : Fin n) (C : G.Walk u u), C.IsCycle ∧
        (∀ a b : Fin n, a ∈ C.support → b ∈ C.support → G.Adj a b → s(a, b) ∈ C.edges) ∧
        (∀ a b : Fin n, a ∉ C.support → b ∉ C.support → ¬ G.Adj a b)) := by
  sorry

end OMA.S_mo_497434
