import Mathlib

/-!
# OEIS A214385: Barker's conjectures for 3 X 3 X 3 triangular 0..n arrays with no element lying outside the (possibly reversed) range delimited by its sw and se neighbors, and no element equal to its horizontal neighbors

Source: https://oeis.org/A214385 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A214385 (R. H. Hardin, Jul 14 2012), offset 1: Number of 3 X 3 X 3 triangular 0..n arrays with no element lying outside the (possibly reversed) range delimited by its sw and se neighbors, and no element equal to its horizontal neighbors.
Formula section:
Empirical: a(n) = (1/36)*n^6 + (7/15)*n^5 + (22/9)*n^4 + (25/6)*n^3 + (55/36)*n^2 - (19/30)*n.
Conjectures from Colin Barker, Jul 22 2018: (Start)
G.f.: 2*x*(4 + 19*x - 17*x^2 + 4*x^3) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* A 3 X 3 X 3 triangular array of 0..n is a map x : Fin 6 -> Fin (n + 1) on its six cells.
* The triangle's six cells are numbered row by row as in the picture of `good`. The
  south-west and south-east neighbors of a cell are the two cells below it, and an
  element lies in the (possibly reversed) range delimited by them when it lies between
  them, ends included.
* The horizontal neighbors of an element are the adjacent cells of its row.
  The entry is row 3 of the table A214384.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^7 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 7, as an identity of integers.
* The definition reproduces the entry's data (8, 94, 456, 1506, 3976, 9044, ... from n = 1, checked by direct
  enumeration for small n and against every listed term through the formula of the proof).
-/

namespace OMA.S_oeis_a214385

open PowerSeries Finset

/-- v lies in the (possibly reversed) range delimited by a and b. -/
def inRange {N : ℕ} (v a b : Fin N) : Prop := (a ≤ v ∧ v ≤ b) ∨ (b ≤ v ∧ v ≤ a)

/-- A 3 X 3 X 3 triangular array has its six cells numbered row by row,
        0
      1   2
    3   4   5
so the south-west and south-east neighbors are 1, 2 for cell 0, 3, 4 for cell 1 and 4, 5 for cell 2
(the bottom row has none). Every element lies in the range delimited by those two neighbors, and no element equals its horizontal neighbor. -/
def good {N : ℕ} (x : Fin 6 → Fin N) : Prop :=
  inRange (x 0) (x 1) (x 2) ∧ inRange (x 1) (x 3) (x 4) ∧ inRange (x 2) (x 4) (x 5) ∧
    x 1 ≠ x 2 ∧ x 3 ≠ x 4 ∧ x 4 ≠ x 5

instance {N : ℕ} : DecidablePred (@good N) := fun x => by unfold good inRange; infer_instance

/-- A214385: the number of 3 X 3 X 3 triangular 0..n arrays with no element lying outside the (possibly reversed) range delimited by its sw and se neighbors, and no element equal to its horizontal neighbors. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 6 → Fin (n + 1))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X * (4 + 19 * X - 17 * X ^ 2 + 4 * X ^ 3) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a214385
