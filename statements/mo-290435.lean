import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace OMA.S_mo_290435

universe u

/-- The quotient that identifies exactly the chosen pair of vertices. -/
abbrev Identified {V : Type u} (u v : V) :=
  Quot (fun x y : V => x = u ∧ y = v)

/-- The graph after identification, with adjacency inherited from representatives. -/
def identify {V : Type u} (G : SimpleGraph V) (u v : V) : SimpleGraph (Identified u v) :=
  let project : V → Identified u v := Quot.mk _
  SimpleGraph.fromRel (fun a b =>
    ∃ x y : V, G.Adj x y ∧ project x = a ∧ project y = b)

/-- A complete minor, expressed by its nonempty connected branch sets. -/
def HasCliqueMinor {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ branch : Fin k → Set V,
    (∀ i, (branch i).Nonempty ∧ (G.induce (branch i)).Preconnected) ∧
    Pairwise (fun i j => Disjoint (branch i) (branch j)) ∧
    ∀ i j, i ≠ j → ∃ x ∈ branch i, ∃ y ∈ branch j, G.Adj x y

/-- A noncomplete graph whose Hadwiger number increases whenever two distinct
nonadjacent vertices are identified. -/
theorem main :
    ∃ n : ℕ, 3 ≤ n ∧ ∃ G : SimpleGraph (Fin n), G ≠ ⊤ ∧
      ∀ u v : Fin n, u ≠ v → ¬ G.Adj u v →
        ∃ k : ℕ, HasCliqueMinor (identify G u v) k ∧ ¬ HasCliqueMinor G k := by
  sorry

end OMA.S_mo_290435
