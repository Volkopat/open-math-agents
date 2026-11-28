import Mathlib

/-!
# OEIS A187303: Hardin's quadratic and Barker's conjectures for 8-step tours

Source: https://oeis.org/A187303 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187303 (R. H. Hardin, Mar 08 2011), offset 1: Number of 8-step one space leftwards or up, two space rightwards or down asymmetric rook's tours on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 9878*n^2 - 79388*n + 143388 for n>13.
Conjectures from Colin Barker, Apr 23 2018: (Start)
G.f.: 2*x^3*(36 + 906*x + 3455*x^2 + 2401*x^3 + 3148*x^4 - 196*x^5 + 1607*x^6 - 1337*x^7 + 579*x^8 - 705*x^9 + 137*x^10 - 155*x^11 + 15*x^12 - 13*x^13) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>16.
(End)

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the rook's moves, one space leftwards or up and two spaces rightwards or down: (-1,0), (0,-1), (2,0), (0,2).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 8-step tour is a sequence of 8 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..8). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 72, 2028, 12778, 37124, 81362, 145100, 231552, 338044, 465734, 613212, 780752 for n = 1..13,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187303

open Finset

/-- Integer coordinates (column, row) of a square of the n X n board. -/
def toZ {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := ((q.1 : ℤ), (q.2 : ℤ))

/-- The moves as displacements (columns to the right, rows downwards): the rook's moves, one space leftwards or up and two spaces rightwards or down. -/
def moves : List (ℤ × ℤ) := [(-1, 0), (0, -1), (2, 0), (0, 2)]

/-- A tour of k squares: k distinct squares of the board, each reached from the previous one by
one of the moves. -/
def IsTour (n k : ℕ) (p : Fin k → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin k, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves

instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance

/-- A187303(n): the 8-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 8 → Fin n × Fin n)).filter (IsTour n 8)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 13 < n → (a n : ℤ) = 9878 * n ^ 2 - 79388 * n + 143388) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 2 * PowerSeries.X ^ 3 * (36 + 906 * PowerSeries.X + 3455 * PowerSeries.X ^ 2 + 2401 * PowerSeries.X ^ 3 + 3148 * PowerSeries.X ^ 4 - 196 * PowerSeries.X ^ 5 + 1607 * PowerSeries.X ^ 6 - 1337 * PowerSeries.X ^ 7 + 579 * PowerSeries.X ^ 8 - 705 * PowerSeries.X ^ 9 + 137 * PowerSeries.X ^ 10 - 155 * PowerSeries.X ^ 11 + 15 * PowerSeries.X ^ 12 - 13 * PowerSeries.X ^ 13) ∧
    (∀ n : ℕ, 16 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187303
