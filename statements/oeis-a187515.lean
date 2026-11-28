import Mathlib

/-!
# OEIS A187515: Hardin's quadratic and Barker's conjectures for 10-step tours

Source: https://oeis.org/A187515 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187515 (R. H. Hardin, Mar 10 2011), offset 1: Number of 10-step S, E, and NW-moving king's tours on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 3603*n^2 - 28504*n + 54377 for n>8.
Conjectures from Colin Barker, Apr 24 2018: (Start)
G.f.: x^4*(398 + 2674*x + 3386*x^2 + 1366*x^3 - 172*x^4 - 324*x^5 - 107*x^6 - 15*x^7) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>11.
(End)

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the king's moves S, E and NW: (0,1), (1,0), (-1,-1).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 10-step tour is a sequence of 10 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..10). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 0, 398, 3868, 13796, 31548, 56952, 89684, 129637, 176796, 231161 for n = 1..12,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187515

open Finset

/-- Integer coordinates (column, row) of a square of the n X n board. -/
def toZ {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := ((q.1 : ℤ), (q.2 : ℤ))

/-- The moves as displacements (columns to the right, rows downwards): the king's moves S, E and NW. -/
def moves : List (ℤ × ℤ) := [(0, 1), (1, 0), (-1, -1)]

/-- A tour of k squares: k distinct squares of the board, each reached from the previous one by
one of the moves. -/
def IsTour (n k : ℕ) (p : Fin k → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin k, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves

instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance

/-- A187515(n): the 10-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 10 → Fin n × Fin n)).filter (IsTour n 10)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 3603 * n ^ 2 - 28504 * n + 54377) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = PowerSeries.X ^ 4 * (398 + 2674 * PowerSeries.X + 3386 * PowerSeries.X ^ 2 + 1366 * PowerSeries.X ^ 3 - 172 * PowerSeries.X ^ 4 - 324 * PowerSeries.X ^ 5 - 107 * PowerSeries.X ^ 6 - 15 * PowerSeries.X ^ 7) ∧
    (∀ n : ℕ, 11 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187515
