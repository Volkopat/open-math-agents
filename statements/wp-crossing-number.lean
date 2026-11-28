import Mathlib

/-!
# Crossing number: rectilinear crossing number and halving lines

Source: https://en.wikipedia.org/wiki/Crossing_number_(graph_theory)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Open problem (Wikipedia): for each arrangement of points in which the rectilinear crossing number
is minimized, is the number of halving lines maximized?

Conventions:
* Point sets are finite sets of `n` points in the plane in general position (no three
  collinear), the setting in which both quantities are studied.
* The rectilinear crossing number of a point set `P` is the number of crossings of the straight
  line drawing of `K_n` on `P`. Each 4-subset in convex position contributes exactly one crossing
  and every other 4-subset none, so it is the number of 4-subsets in convex position (no point
  in the convex hull of the other three).
* A halving line of `P` is a line through two points of `P` that splits the remaining `n - 2`
  points as evenly as possible: the numbers of points strictly on its two sides differ by at most
  one (for even `n` this is the usual `(n-2)/2` on each side).
* "Minimized"/"maximized" are over all `n`-point sets in general position.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_wp_crossing_number

/-- The plane. -/
abbrev P := EuclideanSpace ℝ (Fin 2)

/-- No three points of `A` are collinear. -/
def GeneralPosition (A : Finset P) : Prop :=
  ∀ T ⊆ A, T.card = 3 → ¬ Collinear ℝ (T : Set P)

open Classical in
/-- The rectilinear crossing number of the straight-line drawing of the complete graph on `A`. -/
noncomputable def rectCross (A : Finset P) : ℕ :=
  ((A.powersetCard 4).filter (fun T : Finset P =>
    ∀ x ∈ T, x ∉ convexHull ℝ ((T.erase x : Finset P) : Set P))).card

/-- Orientation of `r` relative to the directed line `p q` (sign of the cross product). -/
def side (p q r : P) : ℝ := (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

open Classical in
/-- The number of halving lines of `A` (unordered pairs `{p, q}` spanning a halving line). -/
noncomputable def halvingLines (A : Finset P) : ℕ :=
  ((A.powersetCard 2).filter (fun T : Finset P => ∃ p ∈ T, ∃ q ∈ T, p ≠ q ∧
    (((A.filter (fun r => 0 < side p q r)).card : ℤ) -
      (A.filter (fun r => side p q r < 0)).card).natAbs ≤ 1)).card

theorem main :
    ∀ A : Finset P, GeneralPosition A →
      (∀ B : Finset P, GeneralPosition B → B.card = A.card → rectCross A ≤ rectCross B) →
      ∀ B : Finset P, GeneralPosition B → B.card = A.card → halvingLines B ≤ halvingLines A := by
  sorry

end OMA.S_wp_crossing_number
