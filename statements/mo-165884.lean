import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
David Speyer, MathOverflow question 165884 (2014).
https://mathoverflow.net/q/165884

The target is the explicit formula in the question. Coordinates identify the
complex plane with pairs of reals and the Gaussian integers with pairs of
integers. A closed simple polygon is described by an ear triangulation, which
also computes its area. The ear representation includes nonconvex polygons.
-/

namespace OMA.S_mo_165884

abbrev Point := ℝ × ℝ

def onGrid (N : ℕ) (p : Point) : Prop :=
  ∃ x y : ℤ, (N : ℝ) * p.1 = x ∧ (N : ℝ) * p.2 = y

noncomputable def determinant (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

def triangle (a b c : Point) : Set Point := fun p =>
  ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧
    p.1 = a.1 + s * (b.1 - a.1) + t * (c.1 - a.1) ∧
    p.2 = a.2 + s * (b.2 - a.2) + t * (c.2 - a.2)

def closedEdge (a b : Point) : Set Point := fun p =>
  ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
    p.1 = a.1 + s * (b.1 - a.1) ∧ p.2 = a.2 + s * (b.2 - a.2)

/-- Glue each new ear along one full edge, with no other intersection.
Reversing ear removal gives such a representation for any simple polygon.
The real index records the sum of the unsigned triangle areas. -/
inductive GridPolygon (N : ℕ) : Set Point → ℝ → Prop where
  | base (a b c : Point) (ha : onGrid N a) (hb : onGrid N b) (hc : onGrid N c)
      (h : determinant a b c ≠ 0) :
      GridPolygon N (triangle a b c) (|determinant a b c| / 2)
  | ear {P : Set Point} {area : ℝ} (prev : GridPolygon N P area)
      (a b c : Point) (ha : onGrid N a) (hb : onGrid N b) (hc : onGrid N c)
      (h : determinant a b c ≠ 0) (shared : P ∩ triangle a b c = closedEdge a b) :
      GridPolygon N (P ∪ triangle a b c) (area + |determinant a b c| / 2)

def inDilation (P : Set Point) (u v : ℤ) (p : ℤ × ℤ) : Prop :=
  ∃ x y : ℝ, (x,y) ∈ P ∧
    (p.1 : ℝ) = (u : ℝ)*x - (v : ℝ)*y ∧
    (p.2 : ℝ) = (v : ℝ)*x + (u : ℝ)*y

noncomputable def latticeCount (P : Set Point) (u v : ℤ) : ℕ :=
  Nat.card {p : ℤ × ℤ // inDilation P u v p}

/-- Existence of a Gaussian-integer Bézout identity for r+si and u+vi. -/
def gaussianCoprime (r s u v : ℤ) : Prop :=
  ∃ a b c d : ℤ, r*a - s*b + u*c - v*d = 1 ∧ r*b + s*a + u*d + v*c = 0

def primitive (u v : ℤ) : Prop := ∃ a b : ℤ, u*a + v*b = 1

def periodic (N : ℕ) (f : ℤ → ℤ → ℝ) : Prop :=
  ∀ u v i j : ℤ, f (u + (N : ℤ)*i) (v + (N : ℤ)*j) = f u v

theorem main : ∀ (N : ℕ), 0 < N → ∀ (P : Set Point) (area : ℝ),
    GridPolygon N P area →
    ∃ r s : ℤ, (r ≠ 0 ∨ s ≠ 0) ∧
      ∃ a b c : ℤ → ℤ → ℝ, periodic N a ∧ periodic N b ∧ periodic N c ∧
        ∀ u v : ℤ, gaussianCoprime r s u v → primitive u v →
          (latticeCount P u v : ℝ) =
            (((u^2 + v^2 : ℤ) : ℝ) * area) + a u v * u + b u v * v + c u v := by
  sorry

end OMA.S_mo_165884
