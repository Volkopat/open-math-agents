import Mathlib

/-!
# OEIS A187049: Hardin's quadratic and Barker's conjectures for 5-step tours

Source: https://oeis.org/A187049 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187049 (R. H. Hardin, Mar 02 2011), offset 1: Number of 5-step one or two space at a time bishop's tours on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 2540*n^2 - 21128*n + 43936 for n>7.
Conjectures from Colin Barker, Apr 20 2018: (Start)
G.f.: 4*x^3*(2 + 108*x + 388*x^2 + 472*x^3 + 308*x^4 + 70*x^5 - 41*x^6 - 37*x^7) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>10.
(End)

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the bishop's moves one or two spaces at a time: (1,1), (1,-1), (-1,1), (-1,-1), (2,2), (2,-2), (-2,2), (-2,-2).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 5-step tour is a sequence of 5 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..5). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 8, 456, 2896, 9216, 20648, 37472, 59524, 86656, 118868 for n = 1..11,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187049

open Finset

/-- Integer coordinates (column, row) of a square of the n X n board. -/
def toZ {n : ℕ} (q : Fin n × Fin n) : ℤ × ℤ := ((q.1 : ℤ), (q.2 : ℤ))

/-- The moves as displacements (columns to the right, rows downwards): the bishop's moves one or two spaces at a time. -/
def moves : List (ℤ × ℤ) := [(1, 1), (1, -1), (-1, 1), (-1, -1), (2, 2), (2, -2), (-2, 2), (-2, -2)]

/-- A tour of k squares: k distinct squares of the board, each reached from the previous one by
one of the moves. -/
def IsTour (n k : ℕ) (p : Fin k → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j : Fin k, j.val = i.val + 1 → toZ (p j) - toZ (p i) ∈ moves

instance (n k : ℕ) : DecidablePred (IsTour n k) := fun p => by unfold IsTour; infer_instance

/-- A187049(n): the 5-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 5 → Fin n × Fin n)).filter (IsTour n 5)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 2540 * n ^ 2 - 21128 * n + 43936) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = 4 * PowerSeries.X ^ 3 * (2 + 108 * PowerSeries.X + 388 * PowerSeries.X ^ 2 + 472 * PowerSeries.X ^ 3 + 308 * PowerSeries.X ^ 4 + 70 * PowerSeries.X ^ 5 - 41 * PowerSeries.X ^ 6 - 37 * PowerSeries.X ^ 7) ∧
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187049
