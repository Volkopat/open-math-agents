import Mathlib

/-!
# OEIS A187382: Hardin's quadratic and Barker's conjectures for 8-step tours

Source: https://oeis.org/A187382 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187382 (R. H. Hardin, Mar 09 2011), offset 1: Number of 8-step S, NW and NE-moving king's tours on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 1297*n^2 - 9679*n + 17420 for n>6.
Conjectures from Colin Barker, Apr 24 2018: (Start)
G.f.: 2*x^4*(202 + 464*x + 586*x^2 + 48*x^3 + 168*x^4 - 171*x^5) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>9.
(End)

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the king's moves S, NW and NE: (0,1), (-1,-1), (1,-1).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 8-step tour is a sequence of 8 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..8). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 0, 404, 2140, 6380, 13220, 22996, 35366, 50330 for n = 1..10,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187382

open Finset

/-- Integer coordinates (column, row) of a square of the n X n board. -/
def toZ {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := ((q.1 : ℤ), (q.2 : ℤ))

/-- The moves as displacements (columns to the right, rows downwards): the king's moves S, NW and NE. -/
def moves : List (ℤ × ℤ) := [(0, 1), (-1, -1), (1, -1)]

/-- A tour of k squares: k distinct squares of the board, each reached from the previous one by
one of the moves. -/
def IsTour (n k : ℕ) (p : Fin k → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin k, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves

instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance

/-- A187382(n): the 8-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 8 → Fin n × Fin n)).filter (IsTour n 8)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 1297 * n ^ 2 - 9679 * n + 17420) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 2 * PowerSeries.X ^ 4 * (202 + 464 * PowerSeries.X + 586 * PowerSeries.X ^ 2 + 48 * PowerSeries.X ^ 3 + 168 * PowerSeries.X ^ 4 - 171 * PowerSeries.X ^ 5) ∧
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187382
