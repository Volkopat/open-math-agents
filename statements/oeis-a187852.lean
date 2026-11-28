import Mathlib

/-!
# OEIS A187852: Hardin's quadratic and Barker's conjectures for 4-step tours

Source: https://oeis.org/A187852 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187852 (R. H. Hardin, Mar 14 2011), offset 1: Number of 4-step king-knight's tours (piece capable of both kinds of moves) on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 3504*n^2 - 17748*n + 21996 for n>5.
Conjectures from Colin Barker, Apr 26 2018: (Start)
G.f.: 4*x^2*(6 + 332*x + 873*x^2 + 567*x^3 + 64*x^4 - 66*x^5 - 24*x^6) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>8.
(End)

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the king's eight moves and the knight's eight moves: (1,0), (-1,0), (0,1), (0,-1), (1,1), (1,-1), (-1,1), (-1,-1), (1,2), (2,1), (-1,2), (-2,1), (1,-2), (2,-1), (-1,-2), (-2,-1).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 4-step tour is a sequence of 4 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..4). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 24, 1400, 7620, 20952, 41652, 69456, 104268, 146088 for n = 1..9,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187852

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

/-- A187852(n): the 4-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 4 → Fin n × Fin n)).filter (IsTour n 4)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 3504 * n ^ 2 - 17748 * n + 21996) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 4 * PowerSeries.X ^ 2 * (6 + 332 * PowerSeries.X + 873 * PowerSeries.X ^ 2 + 567 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 4 - 66 * PowerSeries.X ^ 5 - 24 * PowerSeries.X ^ 6) ∧
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187852
