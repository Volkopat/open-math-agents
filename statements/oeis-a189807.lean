import Mathlib

/-!
# OEIS A189807: Barker's conjectures

Source: https://oeis.org/A189807 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A189807 (R. H. Hardin, Apr 28 2011), offset 1: Number of right triangles on an (n+1) X 3 grid.
Formula section:
Empirical: a(n) = 6*n^2 + 26*n - 42 for n>3.
Conjectures from Colin Barker, May 03 2018: (Start)
G.f.: 2*x*(7 + x + 2*x^2 - 3*x^3 + x^4 - 2*x^5) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>6.
(End)

Formalization notes:
* The (n+1) X 3 grid is the set of points (x, y) with x in 0..2 and y in 0..n, the type
  Fin 3 × Fin (n + 1); a right triangle is a set of three of these points such that the
  two sides at one of them are perpendicular (zero dot product). Three distinct points with
  a right angle are never collinear.
* The statement is Barker's conjectures, the problem as stated on lefttosolve.com: the
  generating function and the recurrence.
* The definition gives a(0) = 0 (the points of one row are collinear), so the generating
  function is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 14, 44, 94, 158, 238, 330, 434, 550, 678, 818, 970, 1134 for n = 1..12,
  the entry's first terms.
-/

namespace OMA.S_oeis_a189807

open Finset

/-- The sides at p of the triangle p q r are perpendicular (their dot product vanishes). -/
def Perp {k m : ℕ} (p q r : Fin k × Fin m) : Prop :=
  ((q.1 : ℤ) - p.1) * ((r.1 : ℤ) - p.1) + ((q.2 : ℤ) - p.2) * ((r.2 : ℤ) - p.2) = 0

/-- Three points of the grid that form a right triangle. -/
def IsRight {k m : ℕ} (T : Finset (Fin k × Fin m)) : Prop :=
  T.card = 3 ∧ ∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ Perp p q r

/-- A189807(n): the right triangles with vertices among the points (x, y) of the
(n+1) X 3 grid, x in 0..2 (column) and y in 0..n (row). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {T : Finset (Fin 3 × Fin (n + 1)) // IsRight T}

/-- The problem as the site states it. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 2 * PowerSeries.X * (7 + PowerSeries.X + 2 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 5) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a189807
