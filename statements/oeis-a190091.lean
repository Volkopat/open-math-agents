import Mathlib

/-!
# OEIS A190091: Barker's conjectures

Source: https://oeis.org/A190091 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A190091 (R. H. Hardin, May 04 2011), offset 1: Number of rhombuses on a (n+1) X 3 grid.
Formula section:
Empirical: a(n) = 2*a(n-1) -2*a(n-3) +a(n-4).
Conjectures from Colin Barker, May 04 2018: (Start)
G.f.: x*(2 + 2*x - 2*x^2 - x^3) / ((1 - x)^3*(1 + x)).
a(n) = (n^2 + 12*n - 4) / 4 for n even.
a(n) = (n^2 + 12*n - 5) / 4 for n odd.
(End)

Formalization notes:
* The (n+1) X 3 grid is the set of points (x, y) with x in 0..2 and y in 0..n, the type
  Fin 3 × Fin (n + 1); a rhombus is a set of four of these points that can be ordered
  cyclically p, q, r, s with four equal sides (squared distances), squares included. Four
  distinct points with four equal sides are never collinear: their diagonals bisect each
  other at a right angle.
* The statement is Barker's conjectures, the problem as stated on lefttosolve.com: the
  generating function and the two closed forms.
* The definition gives a(0) = 0 (the points of one row are collinear), so the generating
  function is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 (1 + x) = N(x) in the formal power series ring over the integers.
* The closed forms "for n even" and "for n odd" are stated for the entry's range n >= 1
  (offset 1).
* Both closed forms divide by 4; they are stated over ℚ, where the division is
  exact.
* Controls proved in the proof file: the definition gives
  2, 6, 10, 15, 20, 26, 32, 39, 46, 54, 62, 71 for n = 1..12, the entry's first terms.
-/

namespace OMA.S_oeis_a190091

open Finset

/-- The squared distance between two points of the grid. -/
def sqd {k m : ℕ} (p q : Fin k × Fin m) : ℤ := ((p.1 : ℤ) - q.1) ^ 2 + ((p.2 : ℤ) - q.2) ^ 2

/-- Four points of the grid that form a rhombus: in some cyclic order p, q, r, s the four sides
are equal. -/
def IsRhombus {k m : ℕ} (T : Finset (Fin k × Fin m)) : Prop :=
  T.card = 4 ∧ ∃ p ∈ T, ∃ q ∈ T, ∃ r ∈ T, ∃ s ∈ T, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
    sqd p q = sqd q r ∧ sqd q r = sqd r s ∧ sqd r s = sqd s p

/-- A190091(n): the rhombuses with vertices among the points (x, y) of the
(n+1) X 3 grid, x in 0..2 (column) and y in 0..n (row). -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {T : Finset (Fin 3 × Fin (n + 1)) // IsRhombus T}

/-- The problem as the site states it. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X)) = PowerSeries.X * (2 + 2 * PowerSeries.X - 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3) ∧
    (∀ n : ℕ, 0 < n → Even n → (a n : ℚ) = ((n : ℚ) ^ 2 + 12 * (n : ℚ) - 4) / 4) ∧
    (∀ n : ℕ, 0 < n → Odd n → (a n : ℚ) = ((n : ℚ) ^ 2 + 12 * (n : ℚ) - 5) / 4) := by
  sorry

end OMA.S_oeis_a190091
