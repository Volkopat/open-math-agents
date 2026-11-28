import Mathlib

/-!
# Erdős Problem 130

Source: https://www.erdosproblems.com/130
Credit: @mgv27

Let $A\subset\mathbb{R}^2$ be an infinite set which contains no three points on a line and no
four points on a circle. Consider the graph with vertices the points in $A$, where two vertices
are joined by an edge if and only if they are an integer distance apart. How large can the
chromatic number and clique number of this graph be? In particular, can the chromatic number be
infinite?

Formalization notes:
* `main` states the specific question "can the chromatic number be infinite?" as the existence
  of such a set `A` whose integer-distance graph has no proper colouring with finitely many
  colours. The vaguer "how large can the chromatic and clique number be" is not stated.
* The plane is `EuclideanSpace ℝ (Fin 2)` with its Euclidean distance.
* "No three points on a line": no three pairwise distinct points of `A` are `Collinear`.
  "No four points on a circle": no four pairwise distinct points of `A` are `Cospherical`
  (in the plane, cospherical means lying on a common circle).
* Edges join distinct points `x ≠ y` of `A` with `dist x y ∈ ℤ`.
* A proper `k`-colouring is a map `A → Fin k` (given as a map on the whole plane, which is
  equivalent) giving distinct colours to adjacent points; chromatic number infinite means no
  such colouring exists for any `k : ℕ`.
* The source notes the graph cannot contain an infinite complete graph (Anning–Erdős: an
  infinite set with all distances integral is collinear).
-/

namespace OMA.S_erdos_130

/-- The plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `A` contains no three pairwise distinct collinear points. -/
def NoThreeOnLine (A : Set Plane) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c → ¬ Collinear ℝ ({a, b, c} : Set Plane)

/-- `A` contains no four pairwise distinct points on a common circle. -/
def NoFourOnCircle (A : Set Plane) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ¬ EuclideanGeometry.Cospherical ({a, b, c, d} : Set Plane)

/-- `f` is a proper colouring of the integer-distance graph on `A`. -/
def ProperColouring (A : Set Plane) {k : ℕ} (f : Plane → Fin k) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∃ m : ℤ, dist x y = m) → f x ≠ f y

/-- Erdős Problem 130: can the integer-distance graph on an infinite planar set with no three
points on a line and no four on a circle have infinite chromatic number? -/
theorem main : ∃ A : Set Plane, A.Infinite ∧ NoThreeOnLine A ∧ NoFourOnCircle A ∧
    ∀ k : ℕ, ¬ ∃ f : Plane → Fin k, ProperColouring A f := by
  sorry

end OMA.S_erdos_130
