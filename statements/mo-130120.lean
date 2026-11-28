import Mathlib

/-!
# Coloring one side of a bipartite graph so that every vertex on the other side sees two colors

Source: https://mathoverflow.net/questions/130120
Credit: @koolkao

Question (Andrea, MathOverflow 130120, 2013; CC BY-SA 3.0). There is a bipartite graph `G` with
the two vertex sets `V1`, `V2`. Each vertex of `V1` is connected to at least `2` vertices of `V2`
and with at most `N` vertices of `V2`. Each vertex of `V2` is connected with some vertex of `V1`.
Is there a function `f(N)` such that choosing `f(N)` colors to color the vertices of `V2` I can
ensure that each vertex of `V1` is connected with at least two vertices of different colors?

`main` states that the answer is yes. A disproof shows that no such function exists: for some
`N`, the number of colors needed is unbounded.

Translation choices:
* the bipartite graph is given by finite vertex sets `V₁`, `V₂` (types with `Fintype`) and an
  adjacency relation `E : V₁ → V₂ → Prop`; the neighborhood of `v ∈ V₁` is `{w | E v w}` and its
  size is `Set.ncard`;
* the colors are `Fin (f N)`, so "choosing `f(N)` colors" allows at most `f(N)` distinct colors;
* "connected with at least two vertices of different colors" is: there are neighbors `w, w'` of
  `v` with `c w ≠ c w'`.
-/

namespace OMA.S_mo_130120

/-- There is `f : ℕ → ℕ` such that whenever every vertex of `V₁` has between `2` and `N`
neighbors in `V₂` and every vertex of `V₂` has a neighbor, the vertices of `V₂` can be colored
with `f N` colors so that every vertex of `V₁` has two neighbors of different colors. -/
theorem main :
    ∃ f : ℕ → ℕ, ∀ (N : ℕ) (V₁ V₂ : Type) [Fintype V₁] [Fintype V₂] (E : V₁ → V₂ → Prop),
      (∀ v, 2 ≤ {w | E v w}.ncard ∧ {w | E v w}.ncard ≤ N) →
      (∀ w, ∃ v, E v w) →
      ∃ c : V₂ → Fin (f N), ∀ v, ∃ w w', E v w ∧ E v w' ∧ c w ≠ c w' := by
  sorry

end OMA.S_mo_130120
