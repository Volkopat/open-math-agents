import OMAStatements.S_opg_monochromatic_reachability_vs_rainbow_triangles

/-!
# Reduction of the Sands–Sauer–Woodrow problem at the two-colour incidence boundary

Galeana-Sánchez and Rojas-Monroy, *Monochromatic paths and at most 2-coloured arc sets in
edge-coloured tournaments* (Graphs and Combinatorics 21, 2005, 307-317), proved the desired
alternative for tournaments in which no vertex is incident with edges of all three colours.
Georgakopoulos and Sprüssel later gave another proof (arXiv:0904.1967).

`H1` is that published special case. `H2` is the complementary open core: some vertex is
incident with all three colours. Incidence is direction-insensitive, while the colour of an
incoming arc `w → v` is read as `col w v`.
-/

namespace OMA.R_opg_monochromatic_reachability_vs_rainbow_triangles_R1

open OMA.S_opg_monochromatic_reachability_vs_rainbow_triangles

/-- The published case: every vertex misses at least one of the three incident arc colours. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) (col : V → V → Fin 3),
    IsTournament G →
    (∀ v : V, ¬ ∀ k : Fin 3, ∃ w : V,
      (G.Adj v w ∧ col v w = k) ∨ (G.Adj w v ∧ col w v = k)) →
    (∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        col a b ≠ col b c ∧ col b c ≠ col c a ∧ col a b ≠ col c a) ∨
    (∃ v : V, ∀ w : V, w ≠ v → ∃ k : Fin 3,
        Relation.TransGen (fun x y => G.Adj x y ∧ col x y = k) v w)

/-- The complementary open case: some vertex is incident with all three colours. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) (col : V → V → Fin 3),
    IsTournament G →
    (∃ v : V, ∀ k : Fin 3, ∃ w : V,
      (G.Adj v w ∧ col v w = k) ∨ (G.Adj w v ∧ col w v = k)) →
    (∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        col a b ≠ col b c ∧ col b c ≠ col c a ∧ col a b ≠ col c a) ∨
    (∃ v : V, ∀ w : V, w ≠ v → ∃ k : Fin 3,
        Relation.TransGen (fun x y => G.Adj x y ∧ col x y = k) v w)

theorem main : H1 → H2 → type_of% @OMA.S_opg_monochromatic_reachability_vs_rainbow_triangles.main := by
  intro h1 h2 V _fin _nonempty G col htour
  by_cases hnone : ∀ v : V, ¬ ∀ k : Fin 3, ∃ w : V,
      (G.Adj v w ∧ col v w = k) ∨ (G.Adj w v ∧ col w v = k)
  · exact h1 V G col htour hnone
  · obtain ⟨v, hv⟩ := not_forall.mp hnone
    exact h2 V G col htour ⟨v, Classical.not_not.mp hv⟩

end OMA.R_opg_monochromatic_reachability_vs_rainbow_triangles_R1
