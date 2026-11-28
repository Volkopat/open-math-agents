import Mathlib

namespace OMA.S_mo_350931

/-- The four paths in the edited MathOverflow diagram, read from top right
to bottom left. Cartesian coordinates increase to the right and upwards. -/
inductive Shape
  | horizontal | vertical | leftDown | downLeft
  deriving DecidableEq

/-- A shape and the lower-left corner of its bounding box. -/
abbrev Placement := Shape × (ℕ × ℕ)

def cells : Placement → Finset (ℕ × ℕ)
  | (.horizontal, x, y) => {(x, y), (x + 1, y), (x + 2, y)}
  | (.vertical, x, y)   => {(x, y), (x, y + 1), (x, y + 2)}
  | (.leftDown, x, y)   => {(x, y), (x, y + 1), (x + 1, y + 1)}
  | (.downLeft, x, y)   => {(x, y), (x + 1, y), (x + 1, y + 1)}

def rectangle (w h : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range w) ×ˢ (Finset.range h)

def Tiles (w h : ℕ) (T : Finset Placement) : Prop :=
  T.biUnion cells = rectangle w h ∧ (T : Set Placement).PairwiseDisjoint cells

def lCount (T : Finset Placement) : ℕ :=
  (T.filter (fun p => p.1 = .leftDown ∨ p.1 = .downLeft)).card

/-- If one tiling of a rectangle uses an even number of L-trominoes, every
tiling of that rectangle by the four allowed shapes does. -/
theorem main :
    ∀ w h : ℕ, 0 < w → 0 < h →
      (∃ T, Tiles w h T ∧ Even (lCount T)) →
      ∀ U, Tiles w h U → Even (lCount U) := by
  sorry

end OMA.S_mo_350931
