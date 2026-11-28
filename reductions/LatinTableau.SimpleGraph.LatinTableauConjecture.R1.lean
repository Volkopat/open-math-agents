import FormalConjectures.Paper.LatinTableau
import Mathlib

/-!
Reduction LatinTableau.SimpleGraph.LatinTableauConjecture.R1: split by the shape of the diagram.

H1 is the rectangular case: the graph of an `a × b` rectangle (the rook's graph) is CDS-colourable.
With `s = min a b` and `t = max a b`, colour the cell `(i, j)` by `(i + j) mod t`. Each colour class
meets every line in the short direction once, so it has exactly `s` cells, and the colours below
`k` cover `s * min k t` cells. Conversely an independent set has at most one cell in each line of
the short direction, so `k` independent sets cover at most `min (k s, s t)` cells. This is the
classical Latin rectangle case of the conjecture, not progress on it.

H2 is the open remainder: Young diagrams that are not rectangles.
-/

namespace OMA.R_LatinTableau_SimpleGraph_LatinTableauConjecture_R1

/-- The Latin Tableau Conjecture for rectangular diagrams. -/
def H1 : Prop :=
  ∀ (μ : YoungDiagram) (a b : ℕ), (∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b) →
    μ.toSimpleGraph.CDSColorable

/-- The open remainder: diagrams that are not rectangles. -/
def H2 : Prop :=
  ∀ (μ : YoungDiagram), (¬ ∃ a b : ℕ, ∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b) →
    μ.toSimpleGraph.CDSColorable

theorem main : H1 → H2 → type_of% @LatinTableau.SimpleGraph.LatinTableauConjecture := by
  intro h1 h2 μ
  by_cases h : ∃ a b : ℕ, ∀ c : ℕ × ℕ, c ∈ μ ↔ c.1 < a ∧ c.2 < b
  · obtain ⟨a, b, hab⟩ := h
    exact h1 μ a b hab
  · exact h2 μ h

end OMA.R_LatinTableau_SimpleGraph_LatinTableauConjecture_R1
