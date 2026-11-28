import Mathlib

/-!
# OEIS A187288: Hardin's quadratic and Barker's conjectures for 3-step tours

Source: https://oeis.org/A187288 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187288 (R. H. Hardin, Mar 08 2011), offset 1: Number of 3-step one or two space at a time rook's tours on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 56*n^2 - 160*n + 72 for n>3.
Conjectures from Colin Barker, Apr 22 2018: (Start)
G.f.: 4*x^2*(2 + 21*x + 7*x^2 + x^3 - 3*x^4) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>6.
(End)

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the rook's moves one or two spaces at a time: (1,0), (-1,0), (0,1), (0,-1), (2,0), (-2,0), (0,2), (0,-2).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 3-step tour is a sequence of 3 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..3). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 8, 108, 328, 672, 1128, 1696, 2376, 3168 for n = 1..9,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187288

open Finset

/-- Integer coordinates (column, row) of a square of the n X n board. -/
def toZ {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := ((q.1 : ℤ), (q.2 : ℤ))

/-- The moves as displacements (columns to the right, rows downwards): the rook's moves one or two spaces at a time. -/
def moves : List (ℤ × ℤ) := [(1, 0), (-1, 0), (0, 1), (0, -1), (2, 0), (-2, 0), (0, 2), (0, -2)]

/-- A tour of k squares: k distinct squares of the board, each reached from the previous one by
one of the moves. -/
def IsTour (n k : ℕ) (p : Fin k → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin k, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves

instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance

/-- A187288(n): the 3-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 3 → Fin n × Fin n)).filter (IsTour n 3)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 56 * n ^ 2 - 160 * n + 72) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 4 * PowerSeries.X ^ 2 * (2 + 21 * PowerSeries.X + 7 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 4) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187288
