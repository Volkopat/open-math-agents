import Mathlib

/-!
# OEIS A187608: Barker's conjectures for 4-step asymmetric quasi-bishop's tours

Source: https://oeis.org/A187608 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187608 (R. H. Hardin, Mar 11 2011), offset 1: Number of 4-step one space for components
leftwards or up, two space for components rightwards or down asymmetric quasi-bishop's tours
(antidiagonal moves become knight moves) on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 55*n^2 - 380*n + 640 for n>5.
Conjectures from Colin Barker, Apr 25 2018:
G.f.: x^4*(28 + 60*x - 8*x^2 + 59*x^3 - 29*x^4) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>8.

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The piece moves on the diagonals, one space for components leftwards or up and two spaces for
  components rightwards or down: (-1,-1) up-left, (2,2) down-right, and the antidiagonal moves
  become the knight moves (2,-1) right-up and (-1,2) left-down. Reflecting the board maps this
  move set to its mirror image and does not change the counts, so the orientation chosen does
  not matter.
* A 4-step tour is a sequence of 4 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..4). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's two conjectures,
  in the integers. The definition gives a(0) = 0 (the empty board has no tours), so the
  generating function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated
  as A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 0, 28, 144, 340, 675, 1120, 1675,
  2340, 3115, 4000 for n = 1..12, the entry's first terms.
-/

namespace OMA.S_oeis_a187608

open Finset

/-- Integer coordinates (column, row) of a square of the n X n board. -/
def toZ {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := ((q.1 : ℤ), (q.2 : ℤ))

/-- The moves as displacements (columns to the right, rows downwards): on the diagonals, one space
for components leftwards or up and two spaces for components rightwards or down, so the
antidiagonal moves become knight moves. -/
def moves : List (ℤ × ℤ) := [(-1, -1), (2, 2), (2, -1), (-1, 2)]

/-- A tour of k squares: k distinct squares of the board, each reached from the previous one by
one of the moves. -/
def IsTour (n k : ℕ) (p : Fin k → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin k, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves

instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance

/-- A187608(n): the 4-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 4 → Fin n × Fin n)).filter (IsTour n 4)).card

/-- Hardin's empirical formula and Barker's generating function and recurrence. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 55 * n ^ 2 - 380 * n + 640) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      PowerSeries.X ^ 4 * (28 + 60 * PowerSeries.X - 8 * PowerSeries.X ^ 2 +
        59 * PowerSeries.X ^ 3 - 29 * PowerSeries.X ^ 4) ∧
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187608
