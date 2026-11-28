import Mathlib

/-!
# Borromean rings

The source asks whether a counterexample to Matthew Cook's conjecture exists.
Each of the three given curves may be independently translated and rotated.
The final placement alone matters. The curves keep their original shapes and sizes.

The reference link uses the three cyclically arranged, mutually perpendicular
2-by-4 rectangular frames described in the source's discussion of lattice links.
Ambient isotopy of their union allows permutations and reversals of the components.

Source: https://en.wikipedia.org/wiki/Borromean_rings
Cook's conjecture, as recorded by Howards: https://arxiv.org/abs/1406.3370
Credit: @konradsiebor
-/

namespace OMA.S_wp_borromean_rings

abbrev Space := Fin 3 → ℝ

/-- A rotation followed by a translation, expressed in Cartesian coordinates. -/
def IsRigidMotion (f : Space → Space) : Prop :=
  ∃ (A : Matrix (Fin 3) (Fin 3) ℝ) (b : Space),
    A.transpose * A = 1 ∧ A.det = 1 ∧ ∀ x, f x = A.mulVec x + b

/-- The circle of radius `r` about the origin in the coordinate plane. -/
def xyCircle (r : ℝ) : Set Space :=
  {p | p 2 = 0 ∧ (p 0) ^ 2 + (p 1) ^ 2 = r ^ 2}

def IsRoundCircle (K : Set Space) : Prop :=
  ∃ (r : ℝ) (f : Space → Space), 0 < r ∧ IsRigidMotion f ∧ f '' (xyCircle r) = K

/-- An ambient isotopy starts at the identity. Forward and inverse maps vary
continuously in time and position. -/
def AmbientIsotopic (K L : Set Space) : Prop :=
  ∃ H : unitInterval → (Space ≃ₜ Space),
    Continuous (fun tx : unitInterval × Space => H tx.1 tx.2) ∧
    Continuous (fun tx : unitInterval × Space => (H tx.1).symm tx.2) ∧
    (∀ x, H 0 x = x) ∧ Set.image (fun x => H 1 x) K = L

/-- An ambient image of the standard unknot is itself a simple closed curve. -/
def IsUnknot (K : Set Space) : Prop :=
  AmbientIsotopic (xyCircle 1) K

/-- Boundary of a rectangle with half-width 1 and half-height 2. -/
def RectangleEdge (s t : ℝ) : Prop :=
  (|s| = 1 ∧ |t| ≤ 2) ∨ (|s| ≤ 1 ∧ |t| = 2)

def borromeanLink : Set Space :=
  {p | (p 2 = 0 ∧ RectangleEdge (p 0) (p 1)) ∨
       (p 0 = 0 ∧ RectangleEdge (p 1) (p 2)) ∨
       (p 1 = 0 ∧ RectangleEdge (p 2) (p 0))}

/-- Does some triple containing a noncircular unknot resist every rigid placement? -/
theorem main :
    ∃ K : Fin 3 → Set Space,
      (∀ i, IsUnknot (K i)) ∧ (∃ i, ¬ IsRoundCircle (K i)) ∧
      ¬ ∃ f : Fin 3 → Space → Space,
        (∀ i, IsRigidMotion (f i)) ∧
        (Pairwise fun i j => Disjoint ((f i) '' (K i)) ((f j) '' (K j))) ∧
        AmbientIsotopic (⋃ i, (f i) '' (K i)) borromeanLink := by
  sorry

end OMA.S_wp_borromean_rings
