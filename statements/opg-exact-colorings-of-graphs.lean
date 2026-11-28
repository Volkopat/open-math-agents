import Mathlib

/-!
# Exact colorings of graphs

Source: https://www.openproblemgarden.org/op/exact_colorings_of_graphs
Credit: @ishaanzee

**Conjecture.** For `c ≥ m ≥ 1`, let `P(c, m)` be the statement that given any exact `c`-coloring
of the edges of a complete countably infinite graph (that is, a coloring with `c` colors all of
which must be used at least once), there exists an exactly `m`-colored countably infinite complete
subgraph. Then `P(c, m)` is true if and only if `m = 1`, `m = 2`, or `c = m`.

(Stacey and Weidl showed that for `m ≥ 3` there is `C(m)` with `P(c, m)` false for all `c ≥ C(m)`.)

Formalization:
* The complete countably infinite graph has vertex set `ℕ`, its edges being the pairs `s(x, y)`
  with `x ≠ y`. A `c`-coloring of its edges is `col : Sym2 ℕ → Fin c` (values on the diagonal are
  irrelevant); it is exact if every color is the color of some edge.
* A countably infinite complete subgraph is spanned by an infinite set `S ⊆ ℕ`; it is exactly
  `m`-colored when the colors of the edges inside `S` form a set of exactly `m` colors.
-/

namespace OMA.S_opg_exact_colorings_of_graphs

/-- The set of colors used on the edges inside `S`. -/
def colorsOn {c : ℕ} (col : Sym2 ℕ → Fin c) (S : Set ℕ) : Set (Fin c) :=
  {k | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ col s(x, y) = k}

/-- `P(c, m)`: every exact `c`-coloring of the edges of `K_ℕ` has an infinite complete subgraph
colored with exactly `m` colors. -/
def P (c m : ℕ) : Prop :=
  ∀ col : Sym2 ℕ → Fin c, colorsOn col Set.univ = Set.univ →
    ∃ S : Set ℕ, S.Infinite ∧ (colorsOn col S).ncard = m

/-- **Conjecture**: for `c ≥ m ≥ 1`, `P(c, m)` holds iff `m = 1`, `m = 2` or `c = m`. -/
theorem main : ∀ c m : ℕ, 1 ≤ m → m ≤ c → (P c m ↔ (m = 1 ∨ m = 2 ∨ c = m)) := by
  sorry

end OMA.S_opg_exact_colorings_of_graphs
