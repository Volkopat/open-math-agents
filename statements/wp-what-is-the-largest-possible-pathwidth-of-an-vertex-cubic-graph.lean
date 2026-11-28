import Mathlib

/-!
# Maximum pathwidth of a cubic graph

Determine the largest possible pathwidth of a finite simple cubic graph on
`n` vertices. Nonempty simple cubic graphs exist for even `n ≥ 4`.
The graph may be disconnected.

A path decomposition is a nonempty sequence of bags. Each vertex appears
in a contiguous interval of bags, and each edge has a bag containing both
endpoints. Width at most `w` means that each bag has at most `w + 1` vertices.

Source: https://en.wikipedia.org/wiki/Pathwidth
Reference: https://doi.org/10.1016/j.ipl.2005.10.012
Credit: @konradsiebor
-/

namespace OMA.S_wp_what_is_the_largest_possible_pathwidth_of_an_vertex_cubic_graph

def HasPathwidthAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) : Prop :=
  ∃ (length : ℕ) (bag : Fin (length + 1) → Finset (Fin n)),
    (∀ v : Fin n, ∃ i, v ∈ bag i) ∧
    (∀ u v : Fin n, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i) ∧
    (∀ (i j k : Fin (length + 1)) (v : Fin n),
      i ≤ j → j ≤ k → v ∈ bag i → v ∈ bag k → v ∈ bag j) ∧
    ∀ i, (bag i).card ≤ w + 1

open Classical in
noncomputable def IsCubicPathwidth (n width : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n),
    G.IsRegularOfDegree 3 ∧ IsLeast {w : ℕ | HasPathwidthAtMost G w} width

theorem main :
    ∃ maximum : ℕ → ℕ, ∀ n : ℕ, 4 ≤ n → Even n →
      IsGreatest {width : ℕ | IsCubicPathwidth n width} (maximum n) := by
  sorry

end OMA.S_wp_what_is_the_largest_possible_pathwidth_of_an_vertex_cubic_graph
