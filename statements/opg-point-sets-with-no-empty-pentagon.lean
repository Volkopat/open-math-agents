import Mathlib

/-!
# Point sets with no empty pentagon

Source: https://www.openproblemgarden.org/op/point_sets_with_no_empty_pentagon
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The source asks to classify the finite planar point sets with no empty pentagon, and lists
yes/no sub-questions. We state the affirmative answer to its second question: the visibility
graphs of finite point sets with no empty pentagon have bounded chromatic number.

Conventions (from the source):
* `P` is a finite set of points in `ℝ²`, not necessarily in general position. Two points
  `x ≠ y` of `P` are visible if the closed segment `[x, y]` contains no other point of `P`;
  this defines the visibility graph of `P`.
* An empty pentagon is a set of 5 points of `P` in strictly convex position (none lies in the
  convex hull of the other four) whose convex hull contains no other point of `P` (strictly
  convex position puts the five points at the vertices; every other point of `P` must avoid
  the closed hull, in particular its interior).
-/

namespace OMA.S_opg_point_sets_with_no_empty_pentagon

/-- The plane. -/
abbrev P2 := EuclideanSpace ℝ (Fin 2)

/-- The visibility graph of `P`. -/
def visibility (P : Set P2) : SimpleGraph P :=
  SimpleGraph.fromRel fun x y => ∀ z ∈ P, z ∈ segment ℝ (x : P2) y → z = x ∨ z = y

/-- `P` contains an empty pentagon. -/
def HasEmptyPentagon (P : Set P2) : Prop :=
  ∃ Q : Finset P2, Q.card = 5 ∧ ↑Q ⊆ P ∧
    (∀ q ∈ Q, q ∉ convexHull ℝ (↑(Q.erase q) : Set P2)) ∧
    ∀ z ∈ P, z ∈ convexHull ℝ (↑Q : Set P2) → z ∈ Q

theorem main :
    ∃ c : ℕ, ∀ P : Set P2, P.Finite → ¬ HasEmptyPentagon P →
      (visibility P).chromaticNumber ≤ c := by
  sorry

end OMA.S_opg_point_sets_with_no_empty_pentagon
