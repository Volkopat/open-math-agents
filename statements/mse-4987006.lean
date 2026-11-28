import Mathlib

/-!
# Are cage graphs Hamiltonian?

Source: https://math.stackexchange.com/questions/4987006

An `(r, g)`-cage is an `r`-regular graph of girth `g` with the least possible number of vertices.
The asker observes that every known cage is Hamiltonian, with the exception of the Petersen
graph (the unique `(3, 5)`-cage), and asks how one would prove this; cages are considered for
`r ≥ 3`.

`main` states the conjecture: for `r ≥ 3`, every `(r, g)`-cage that is not isomorphic to the
Petersen graph is Hamiltonian.

Formalization notes:
* A cage on `n` vertices is a `SimpleGraph (Fin n)` that is `r`-regular, has girth `g`, and such
  that no `r`-regular graph of girth `g` has fewer vertices. Girth is Mathlib's extended girth
  `SimpleGraph.egirth`, so an acyclic graph (girth `⊤`) is never a cage of a finite girth `g`.
* The Petersen graph is the Kneser graph `K(5, 2)`: the `2`-element subsets of `Fin 5`, adjacent
  when disjoint.
* Hamiltonicity is Mathlib's `SimpleGraph.IsHamiltonian`.
-/

namespace OMA.S_mse_4987006

/-- The vertices of the Petersen graph: `2`-element subsets of `Fin 5`. -/
abbrev PetersenVertex : Type := {s : Finset (Fin 5) // s.card = 2}

/-- The Petersen graph `K(5, 2)`: two `2`-subsets of `Fin 5` are adjacent iff they are disjoint. -/
def petersenGraph : SimpleGraph PetersenVertex where
  Adj s t := Disjoint s.1 t.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun s h => by
    have hc := s.2
    rw [disjoint_self.mp h] at hc
    simp at hc⟩

open Classical in
/-- `G` is an `(r, g)`-cage: an `r`-regular graph of girth `g` on `n` vertices, and no `r`-regular
graph of girth `g` has fewer than `n` vertices. -/
noncomputable def IsCage (r g n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  G.IsRegularOfDegree r ∧ G.egirth = g ∧
    ∀ m < n, ∀ H : SimpleGraph (Fin m), ¬ (H.IsRegularOfDegree r ∧ H.egirth = g)

/-- Every `(r, g)`-cage with `r ≥ 3` other than the Petersen graph is Hamiltonian. -/
theorem main : ∀ r g n : ℕ, 3 ≤ r → ∀ G : SimpleGraph (Fin n), IsCage r g n G →
    IsEmpty (G ≃g petersenGraph) → G.IsHamiltonian := by
  sorry

end OMA.S_mse_4987006
