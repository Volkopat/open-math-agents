import Mathlib

/-!
# OEIS A374594: integer trapezoids with one pair of parallel sides and area equal to perimeter

Source: https://oeis.org/A374594 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Felix Huber, Jul 13 2024), offset 1: Areas of trapezoids with integer sides, height and
offsets whose area equals their perimeter. A trapezoid is a quadrilateral with at least one pair of
parallel sides. Conjecture: in this sequence are only four terms which belong to trapezoids with
exactly one pair of parallel sides: a(2) = 18, a(4) = 20, a(6) = 24, a(7) = 30.

Formalization notes:
* A trapezoid is described by its parallel sides `a` (lower) and `c` (upper), its height `h` and
  the signed offsets `x`, `y` of its legs: the vertices are (0,0), (a,0), (x+c,h), (x,h), so
  `x + y = a - c`, and the legs `d`, `b` satisfy `d^2 = h^2 + x^2`, `b^2 = h^2 + y^2`. This is the
  parametrization of the entry's Maple program (which takes `x ≥ 0` and `y = a - c - x`).
* Exactly one pair of parallel sides means `a ≠ c`; we take `a > c` (the longer base below), which
  loses nothing since turning a trapezoid upside down swaps its bases.
* Integer sides, height and offsets: all seven numbers are integers, with `c ≥ 1` and `h ≥ 1`.
* Area equals perimeter: `(a + c) h / 2 = a + b + c + d`, written as `(a + c) h = 2 (a + b + c + d)`.
* The conjecture says that exactly four such trapezoids exist and that their areas are 18, 20, 24
  and 30. A reflection (swapping `x` with `y` and `b` with `d`) gives a congruent trapezoid, so
  `main` lists the solutions `(a, c, h, x, y, b, d)` as the four trapezoids together with the mirror
  images of the two that are not isosceles: `(6,3,4,3,0,4,5)` and its mirror (area 18),
  `(8,2,4,3,3,5,5)` (area 20), `(10,6,3,4,0,3,5)` and its mirror (area 24), `(14,6,3,4,4,5,5)`
  (area 30). These are the terms a(2), a(4), a(6), a(7) of the entry.
-/

namespace OMA.S_oeis_a374594

/-- An integer trapezoid with exactly one pair of parallel sides whose area equals its perimeter:
parallel sides `a > c ≥ 1`, height `h ≥ 1`, signed offsets `x`, `y` with `x + y = a - c`, legs
`d, b ≥ 0` with `d^2 = h^2 + x^2`, `b^2 = h^2 + y^2`, and `(a + c) h / 2 = a + b + c + d`. -/
def IsSol (a c h x y b d : ℤ) : Prop :=
  1 ≤ c ∧ c < a ∧ 1 ≤ h ∧ 0 ≤ b ∧ 0 ≤ d ∧ x + y = a - c ∧ d ^ 2 = h ^ 2 + x ^ 2 ∧
    b ^ 2 = h ^ 2 + y ^ 2 ∧ (a + c) * h = 2 * (a + b + c + d)

/-- The six solutions `(a, c, h, x, y, b, d)`: four trapezoids and the mirror images of the two
that are not isosceles. -/
def sols : List (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) :=
  [(6, 3, 4, 3, 0, 4, 5), (6, 3, 4, 0, 3, 5, 4), (8, 2, 4, 3, 3, 5, 5),
    (10, 6, 3, 4, 0, 3, 5), (10, 6, 3, 0, 4, 5, 3), (14, 6, 3, 4, 4, 5, 5)]

/-- Huber's conjecture: the integer trapezoids with exactly one pair of parallel sides and area
equal to perimeter are exactly the listed ones. -/
theorem main : ∀ a c h x y b d : ℤ, IsSol a c h x y b d ↔ (a, c, h, x, y, b, d) ∈ sols := by
  sorry

end OMA.S_oeis_a374594
