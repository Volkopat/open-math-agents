import Mathlib

/-!
# Unique Hamiltonicity for one-ended regular graphs

Mohar asks whether some locally finite one-ended graph of regular degree greater
than two has exactly one Hamiltonian circle. In a one-ended graph, Hamiltonian
circles correspond to spanning double rays.

[Open Problem Garden](https://www.openproblemgarden.org/op/infinite_uniquely_hamiltonian_graphs)
[Mohar, Problem 2](https://www.sfu.ca/~mohar/Problems/P0703_HamiltonicityInfinite.html)
-/

namespace OMA.S_opg_infinite_uniquely_hamiltonian_graphs

def HasOneEnd (G : SimpleGraph ℕ) : Prop :=
  ∀ removed : Finset ℕ,
    let remaining := G.induce (removed : Set ℕ)ᶜ
    ∃! component : remaining.ConnectedComponent, component.supp.Infinite

def IsSpanningDoubleRay (G : SimpleGraph ℕ) (edges : Set (Sym2 ℕ)) : Prop :=
  ∃ vertices : ℤ ≃ ℕ,
    (∀ i : ℤ, G.Adj (vertices i) (vertices (i + 1))) ∧
    edges = Set.range (fun i : ℤ => s(vertices i, vertices (i + 1)))

theorem main :
    ∃ (r : ℕ) (G : SimpleGraph ℕ),
      2 < r ∧ G.Connected ∧
      (∀ v : ℕ, (G.neighborSet v).Finite ∧ (G.neighborSet v).ncard = r) ∧
      HasOneEnd G ∧ ∃! edges : Set (Sym2 ℕ), IsSpanningDoubleRay G edges := by
  sorry

end OMA.S_opg_infinite_uniquely_hamiltonian_graphs
