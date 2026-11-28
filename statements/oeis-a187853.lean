import Mathlib

/-!
# OEIS A187853: Hardin's quadratic and Barker's conjectures for 5-step tours

Source: https://oeis.org/A187853 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187853 (R. H. Hardin, Mar 14 2011), offset 1: Number of 5-step king-knight's tours (piece capable of both kinds of moves) on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 50128*n^2 - 312688*n + 476944 for n>7.
Conjectures from Colin Barker, Apr 26 2018: (Start)
G.f.: 8*x^3*(666 + 4224*x + 5462*x^2 + 2616*x^3 + 237*x^4 - 419*x^5 - 217*x^6 - 37*x^7) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>10.
(End)

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the king's eight moves and the knight's eight moves: (1,0), (-1,0), (0,1), (0,-1), (1,1), (1,-1), (-1,1), (-1,-1), (1,2), (2,1), (-1,2), (-2,1), (1,-2), (2,-1), (-1,-2), (-2,-1).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 5-step tour is a sequence of 5 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..5). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 5328, 49776, 177040, 408048, 744696, 1183632, 1723120, 2362864, 3102864 for n = 1..11,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187853

open Finset

/-- Integer coordinates (column, row) of a square of the n X n board. -/
def toZ {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := ((q.1 : ℤ), (q.2 : ℤ))

/-- The moves as displacements (columns to the right, rows downwards): the king's eight moves and the knight's eight moves. -/
def moves : List (ℤ × ℤ) := [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1), (1, 2), (2, 1), (-1, 2), (-2, 1), (1, -2), (2, -1), (-1, -2), (-2, -1)]

/-- A tour of k squares: k distinct squares of the board, each reached from the previous one by
one of the moves. -/
def IsTour (n k : ℕ) (p : Fin k → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin k, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves

instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance

/-- A187853(n): the 5-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 5 → Fin n × Fin n)).filter (IsTour n 5)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 50128 * n ^ 2 - 312688 * n + 476944) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 8 * PowerSeries.X ^ 3 * (666 + 4224 * PowerSeries.X + 5462 * PowerSeries.X ^ 2 + 2616 * PowerSeries.X ^ 3 + 237 * PowerSeries.X ^ 4 - 419 * PowerSeries.X ^ 5 - 217 * PowerSeries.X ^ 6 - 37 * PowerSeries.X ^ 7) ∧
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187853
