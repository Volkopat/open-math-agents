import Mathlib

namespace OMA.S_mo_106464

abbrev Alphabet := Computability.Γ'

/-- A finite simple graph represented by its Boolean adjacency matrix. -/
structure GraphInput where
  order : ℕ
  adjacency : Fin order → Fin order → Bool
  symmetric : ∀ u v, adjacency u v = adjacency v u
  loopless : ∀ v, ¬ adjacency v v

def GraphInput.graph (G : GraphInput) : SimpleGraph (Fin G.order) :=
  SimpleGraph.mk' ⟨G.adjacency, G.symmetric, G.loopless⟩

def encodeGraph (G : GraphInput) : List Alphabet :=
  (Computability.encodeNat G.order).map Computability.Γ'.bit ++ [.comma] ++
    (List.ofFn fun u : Fin G.order =>
      List.ofFn fun v : Fin G.order => Computability.Γ'.bit (G.adjacency u v)).flatten

def encodePair (input : GraphInput × GraphInput) : List Alphabet :=
  encodeGraph input.1 ++ encodeGraph input.2

/-- Hamiltonian cycles in simple graphs have at least three vertices. -/
def HasHamiltonianCycle (G : GraphInput) : Prop :=
  3 ≤ G.order ∧ G.graph.IsHamiltonian

/-- Can a polynomial-time algorithm distinguish isomorphic pairs from pairs
with exactly one Hamiltonian graph, under the promise of these two cases? -/
theorem main :
    ∃ answer : GraphInput × GraphInput → Bool,
      Nonempty (Turing.TM2ComputableInPolyTime encodePair
        (fun b : Bool => [Computability.Γ'.bit b]) answer) ∧
      ∀ G H : GraphInput,
        let isomorphic := Nonempty (G.graph ≃g H.graph)
        let exactlyOne :=
          (HasHamiltonianCycle G ∧ ¬ HasHamiltonianCycle H) ∨
          (HasHamiltonianCycle H ∧ ¬ HasHamiltonianCycle G)
        (isomorphic ∨ exactlyOne) → (answer (G, H) = true ↔ isomorphic) := by
  sorry

end OMA.S_mo_106464
