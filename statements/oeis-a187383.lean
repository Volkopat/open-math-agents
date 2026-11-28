import Mathlib

/-!
# OEIS A187383: Hardin's quadratic and Barker's conjectures for 9-step tours

Source: https://oeis.org/A187383 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A187383 (R. H. Hardin, Mar 09 2011), offset 1: Number of 9-step S, NW and NE-moving king's tours on an n X n board summed over all starting positions.
Formula section:
Empirical: a(n) = 3385*n^2 - 28390*n + 56892 for n>7.
Conjectures from Colin Barker, Apr 24 2018: (Start)
G.f.: x^4*(340 + 2040*x + 2160*x^2 + 2772*x^3 - 364*x^4 + 687*x^5 - 865*x^6) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>10.
(End)

Formalization notes:
* Squares are pairs (column, row) of Fin n, columns numbered to the right and rows downwards.
  The moves are the king's moves S, NW and NE: (0,1), (-1,-1), (1,-1).
  Reflecting the board maps the move set to its mirror image and does not change the counts, so
  the orientation chosen does not matter.
* A 9-step tour is a sequence of 9 distinct squares, each reached from the previous one by a
  move, as in the entry's examples (the squares of a tour are labeled 1..9). Summing over all
  starting positions means counting all such sequences.
* The statement is the conjunction of Hardin's empirical formula and Barker's conjectures, in the
  integers. The definition gives a(0) = 0 (the empty board has no tours), so the generating
  function of the entry is A(x) = Sum_{n >= 0} a(n) x^n, and the identity is stated as
  A(x) (1 - x)^3 = N(x) in the formal power series ring over the integers.
* Controls proved in the proof file: the definition gives 0, 0, 0, 340, 3060, 10320, 24892, 46412, 75567, 111492, 154187 for n = 1..11,
  the entry's first terms.
-/

namespace OMA.S_oeis_a187383

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

/-- A187383(n): the 9-step tours on the n X n board, over all starting squares. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin 9 → Fin n × Fin n)).filter (IsTour n 9)).card

/-- Hardin's empirical formula and Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 3385 * n ^ 2 - 28390 * n + 56892) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 = PowerSeries.X ^ 4 * (340 + 2040 * PowerSeries.X + 2160 * PowerSeries.X ^ 2 + 2772 * PowerSeries.X ^ 3 - 364 * PowerSeries.X ^ 4 + 687 * PowerSeries.X ^ 5 - 865 * PowerSeries.X ^ 6) ∧
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a187383
