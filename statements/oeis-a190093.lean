import Mathlib

/-!
# OEIS A190093: Barker's conjectures

Source: https://oeis.org/A190093 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A190093 (R. H. Hardin, May 04 2011), offset 1: Number of rhombuses on an (n+1) X 5 grid.
Formula section:
Empirical: a(n) = 2*a(n-1) -2*a(n-3) +a(n-4) for n>11.
Conjectures from Colin Barker, May 04 2018: (Start)
G.f.: x*(4 + 7*x + 6*x^2 + 2*x^3 - 10*x^4 - 5*x^5 + 2*x^7 + 4*x^8 - 2*x^9 - 4*x^10) / ((1 - x)^3*(1 + x)).
a(n) = n^2 + 28*n - 84 for n>7 and even.
a(n) = n^2 + 28*n - 85 for n>7 and odd.
(End)

Formalization notes:
* The (n+1) X 5 grid is the set of points (x, y) with x in 0..4 and y in 0..n, the type
  Fin 5 × Fin (n + 1); a rhombus is a set of four of these points that can be ordered
  cyclically p, q, r, s with four equal sides (squared distances), squares included. Four
  distinct points with four equal sides are never collinear: their diagonals bisect each
  other at a right angle.
* The statement is Barker's conjectures, the problem as stated on lefttosolve.com: the
  generating function and the two closed forms.
* The definition gives a(0) = 0 (the points of one row are collinear), so the generating
  function is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 (1 + x) = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives
  4, 15, 36, 66, 96, 130, 164, 204, 248, 296, 344, 396 for n = 1..12, the entry's first terms.
-/

namespace OMA.S_oeis_a190093

open Finset

/-- The squared distance between two points of the grid. -/
def sqd {k m : ℕ} (p q : Fin k × Fin m) : ℤ := ((p.1 : ℤ) - q.1) ^ 2 + ((p.2 : ℤ) - q.2) ^ 2

/-- Four points of the grid that form a rhombus: in some cyclic order p, q, r, s the four sides
are equal. -/
def IsRhombus {k m : ℕ} (T : Finset (Fin k × Fin m)) : Prop :=
  T.card = 4 ∧ ∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T, ∃ s ∈ T, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
    sqd p q = sqd q r ∧ sqd q r = sqd r s ∧ sqd r s = sqd s p

/-- A190093(n): the rhombuses with vertices among the points (x, y) of the
(n+1) X 5 grid, x in 0..4 (column) and y in 0..n (row). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {T : Finset (Fin 5 × Fin (n + 1)) // IsRhombus T}

/-- The problem as the site states it. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X)) = PowerSeries.X * (4 + 7 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 3 - 10 * PowerSeries.X ^ 4 - 5 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 7 + 4 * PowerSeries.X ^ 8 - 2 * PowerSeries.X ^ 9 - 4 * PowerSeries.X ^ 10) ∧
    (∀ n : ℕ, 7 < n → Even n → (a n : ℤ) = (n : ℤ) ^ 2 + 28 * (n : ℤ) - 84) ∧
    (∀ n : ℕ, 7 < n → Odd n → (a n : ℤ) = (n : ℤ) ^ 2 + 28 * (n : ℤ) - 85) := by
  sorry

end OMA.S_oeis_a190093
