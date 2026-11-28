import Mathlib

/-!
# Star chromatic index of complete graphs

Source: https://www.openproblemgarden.org/op/star_chromatic_index_of_complete_graphs
Credit: @ishaanzee

**Conjecture** (Dvořák, Mohar, Šámal). Is it possible to color edges of the complete graph
`K_n` using `O(n)` colors, so that the coloring is proper and no 4-cycle and no 4-edge path is
using only two colors? Equivalently: is the star chromatic index of `K_n` linear in `n`?

Formalization (affirmative form):
* The vertices of `K_n` are `Fin n`; every pair of distinct vertices is an edge, and an edge
  coloring with `m` colors is a map `col : Sym2 (Fin n) → Fin m` (its values on the diagonal
  `s(v, v)`, which are not edges, play no role).
* Proper: two edges sharing a vertex get different colors.
* A 4-edge path `v₀ v₁ v₂ v₃ v₄` (distinct vertices) or a 4-cycle `v₀ v₁ v₂ v₃ v₀` (distinct
  vertices) uses only two colors in a proper coloring exactly when its colors alternate, i.e.
  the first and third edges have the same color and so do the second and fourth.
* `O(n)` colors: there is a constant `C` such that `K_n` has such a coloring with `C * n` colors
  for every `n`.
-/

namespace OMA.S_opg_star_chromatic_index_of_complete_graphs

/-- `col` is a star edge coloring of `K_n`: proper, and no path or cycle with four edges is
two-colored. -/
def IsStarEdgeColoring {n m : ℕ} (col : Sym2 (Fin n) → Fin m) : Prop :=
  (∀ v : Fin 3 → Fin n, Function.Injective v → col s(v 0, v 1) ≠ col s(v 1, v 2)) ∧
  (∀ v : Fin 5 → Fin n, Function.Injective v →
    ¬ (col s(v 0, v 1) = col s(v 2, v 3) ∧ col s(v 1, v 2) = col s(v 3, v 4))) ∧
  (∀ v : Fin 4 → Fin n, Function.Injective v →
    ¬ (col s(v 0, v 1) = col s(v 2, v 3) ∧ col s(v 1, v 2) = col s(v 3, v 0)))

/-- **The star chromatic index of `K_n` is `O(n)`**. -/
theorem main : ∃ C : ℕ, ∀ n : ℕ, ∃ col : Sym2 (Fin n) → Fin (C * n), IsStarEdgeColoring col := by
  sorry

end OMA.S_opg_star_chromatic_index_of_complete_graphs
