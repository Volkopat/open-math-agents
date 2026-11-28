import Mathlib

/-!
# Hamiltonicity of Cayley graphs

Source: http://www.openproblemgarden.org/op/hamiltonicity_of_cayley_graphs
Credit: @shc261392

Question (Rapaport-Strasser): is every Cayley graph Hamiltonian?

Reading used here (the standard conventions of the question, as in the Curran–Gallian survey the
source cites):
* The group `G` is finite and the Cayley graph is the undirected simple graph of a generating
  set `S`: `a` and `b` are adjacent when `a ≠ b` and `a⁻¹ * b ∈ S` or `b⁻¹ * a ∈ S`. So the graph
  is the usual Cayley graph of `S ∪ S⁻¹` without loops, and it is connected because `S`
  generates `G`.
* The group has at least `3` elements: a cycle needs `3` vertices, and the Cayley graphs of the
  groups of order `1` and `2` are a single vertex and a single edge.
* Hamiltonian is Mathlib's `SimpleGraph.IsHamiltonian`. The statement is the affirmative answer;
  a proof of its negation answers the question in the negative.
-/

namespace OMA.S_opg_hamiltonicity_of_cayley_graphs

/-- The undirected Cayley graph of `S` in the group `G`: by `SimpleGraph.fromRel`, `a` and `b`
are adjacent iff `a ≠ b ∧ (a⁻¹ * b ∈ S ∨ b⁻¹ * a ∈ S)`. -/
def cayley {G : Type} [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel fun a b => a⁻¹ * b ∈ S

theorem main :
    ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G], 3 ≤ Fintype.card G →
      ∀ S : Set G, Subgroup.closure S = ⊤ → (cayley S).IsHamiltonian := by
  sorry

end OMA.S_opg_hamiltonicity_of_cayley_graphs
