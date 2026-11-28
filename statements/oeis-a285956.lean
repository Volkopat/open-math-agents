import Mathlib

/-!
# OEIS A285956: Barker's generating function, closed forms and recurrence

Source: https://oeis.org/A285956 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Rick L. Shepherd, Apr 29 2017), offset 0: Number of orthogonal rectangles with vertices on
an n X n square grid of points but with no vertices on the grid's diagonals. Data: 0, 0, 0, 0, 2,
10, 30, 102, 204, 444, ... The formula section states: Conjectures from Colin Barker, May 03 2017:
(Start) G.f.: 2*x^4*(1 + 3*x + 3*x^2 + 17*x^3) / ((1 - x)^5*(1 + x)^3). a(n) = (n^4 - 10*n^3 +
33*n^2 - 34*n) / 4 for n even. a(n) = (n^4 - 10*n^3 + 37*n^2 - 58*n + 30) / 4 for n odd. a(n) =
2*a(n-1) + 2*a(n-2) - 6*a(n-3) + 6*a(n-5) - 2*a(n-6) - 2*a(n-7) + a(n-8) for n>7. (End)

Formalization notes:
* The grid is the set of points (p, q) with p, q in 0..n-1. An orthogonal rectangle is a rectangle
  with sides parallel to the axes and positive area; it is determined by its x-coordinates x < y
  and its y-coordinates u < v, and its vertices are (x, u), (x, v), (y, u), (y, v). The diagonals of
  the grid are the lines p = q and p + q = n - 1; the latter is written p + q + 1 ≠ n, so that no
  subtraction appears. `good n x y u v` says that no vertex lies on either diagonal, and `a n`
  counts the quadruples (x, y, u, v) in (0..n-1)^4 with `good`. This reading reproduces all 45
  listed terms.
* The g.f. is A(x) = Sum_{n >= 0} a(n) x^n (offset 0), stated as
  A(x) (1 - x)^5 (1 + x)^3 = 2x^4 (1 + 3x + 3x^2 + 17x^3) in Z[[x]], which is equivalent because
  (1 - x)^5 (1 + x)^3 has constant term 1. The closed forms are stated in the rationals for every
  even and every odd n (they give 0 for n < 4, as the data does), and the recurrence in the
  integers for n > 7.
* `main` is the conjunction of Barker's four conjectures.
* Controls proved in the proof file: a(0..44), all the entry's listed terms.
-/

namespace OMA.S_oeis_a285956

open PowerSeries

/-- The axis-parallel rectangle with corners (x, u), (x, v), (y, u), (y, v), where x < y and
u < v, has no corner on a diagonal of the n X n grid of points with coordinates 0..n-1: no corner
(p, q) has p = q (the main diagonal) or p + q = n - 1, written p + q + 1 ≠ n (the other diagonal). -/
def good (n x y u v : ℕ) : Prop :=
  x < y ∧ u < v ∧ x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v ∧
    x + u + 1 ≠ n ∧ x + v + 1 ≠ n ∧ y + u + 1 ≠ n ∧ y + v + 1 ≠ n

instance (n x y u v : ℕ) : Decidable (good n x y u v) := by
  unfold good
  infer_instance

/-- A285956(n): the number of such rectangles, each given by its coordinates (x, y, u, v). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n ×ˢ Finset.range n ×ˢ Finset.range n).filter
    fun q => good n q.1 q.2.1 q.2.2.1 q.2.2.2).card

/-- Barker's conjectures: the g.f., the closed forms for even and odd n, and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 5 * (1 + X) ^ 3) =
      2 * X ^ 4 * (1 + 3 * X + 3 * X ^ 2 + 17 * X ^ 3) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = ((n : ℚ) ^ 4 - 10 * n ^ 3 + 33 * n ^ 2 - 34 * n) / 4) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = ((n : ℚ) ^ 4 - 10 * n ^ 3 + 37 * n ^ 2 - 58 * n + 30) / 4) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) + 6 * a (n - 5) -
      2 * a (n - 6) - 2 * a (n - 7) + a (n - 8) := by
  sorry

end OMA.S_oeis_a285956
