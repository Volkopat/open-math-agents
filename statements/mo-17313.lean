import Mathlib

/-!
# Dissecting a disk into congruent pieces with the centre inside one piece

Source: https://mathoverflow.net/questions/17313
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (MathOverflow; listed in Croft–Falconer–Guy, Unsolved Problems in Geometry): is it
possible to dissect the interior of a circle into a finite number of congruent pieces (mirror
images allowed) such that some neighbourhood of the origin is contained in just one of the
pieces?

Conventions:
* The interior of the circle is the open unit disk in `ℝ²`. A dissection is a partition into
  finitely many pairwise disjoint pieces with union the disk; no regularity is imposed on the
  pieces (the source's main question allows arbitrary sets; connectedness is an optional extra
  constraint mentioned there).
* Congruent: every piece is the image of the first piece under an isometry of the plane
  (reflections allowed).
* At least two pieces (a single piece is the whole disk, which is trivial).
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_17313

/-- The plane. -/
abbrev P := EuclideanSpace ℝ (Fin 2)

theorem main :
    ∃ (k : ℕ) (A : Fin (k + 2) → Set P),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = Metric.ball (0 : P) 1 ∧
      (∀ i, ∃ φ : P ≃ᵢ P, A i = φ '' A 0) ∧
      ∃ i, ∃ ε > 0, Metric.ball (0 : P) ε ⊆ A i := by
  sorry

end OMA.S_mo_17313
