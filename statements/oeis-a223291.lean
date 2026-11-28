import Mathlib

/-!
# OEIS A223291: Barker's g.f. and closed form for n X 2 colorings by the 4-loop graph

Source: https://oeis.org/A223291 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Mar 19 2013), offset 1: 4-loop graph coloring a rectangular array: number
of n X 2 0..8 arrays where 0..8 label nodes of a graph with edges 0,1 1,2 2,0 0,3 3,4 4,0 0,5 5,6
6,0 0,7 7,8 8,0 and every array movement to a horizontal or vertical neighbor moves along an edge
of this graph. Data: 24, 168, 1368, 11304, 93528, ... Formula: Empirical: a(n) = 9*a(n-1) -
6*a(n-2). Conjectures from Colin Barker, Aug 19 2018: G.f.: 24*x*(1 - 2*x) / (1 - 9*x + 6*x^2).
a(n) = (2^(2-n)*((9-sqrt(57))^n*(3+sqrt(57)) + (-3+sqrt(57))*(9+sqrt(57))^n)) / sqrt(57).

Formalization notes:
* An n X 2 array is a function f from the rows Fin n to the rows of two entries Fin 2 -> 0..8.
  Its neighbour pairs are the two entries of a row (horizontal) and the entries in the same
  column of rows i and i + 1 (vertical); a move along an edge means that the two labels are
  joined by one of the twelve listed edges (in either direction), so each neighbour pair is
  required once, in one direction.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1). The identity A(x) = N(x)/D(x) is stated as
  A(x)*D(x) = N(x) in Q[[x]], which is equivalent because D has constant term 1.
* The closed form is stated in the reals for every n >= 1, with 2^(2-n) the real power.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..14) = 24, 168, 1368, 11304, 93528, 773928, 6404184,
  52994088, 438521688, 3628730664, 30027445848, 248474628648, 2056106982744, 17014115072808,
  the entry's data.
-/

namespace OMA.S_oeis_a223291

open PowerSeries Finset

/-- The edges of the 4-loop graph on 0..8 (four triangles sharing the node 0). -/
def edges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 0), (0, 3), (3, 4), (4, 0), (0, 5), (5, 6), (6, 0), (0, 7), (7, 8), (8, 0)]

/-- Two labels are adjacent when they are joined by an edge of the graph. -/
def adj (x y : Fin 9) : Prop := (x.val, y.val) ∈ edges ∨ (y.val, x.val) ∈ edges

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- A223291: the number of n X 2 arrays f (f i j is the entry in row i and column j) with
entries 0..8 in which every move to a horizontal neighbour (column 0 to column 1 of a row) and
every move to a vertical neighbour (row i to row i + 1 of a column) is along an edge. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 2 → Fin 9)).filter
    (fun f => (∀ i : Fin n, adj (f i 0) (f i 1)) ∧
      ∀ i i' : Fin n, i'.val = i.val + 1 → ∀ j : Fin 2, adj (f i j) (f i' j))).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 9 * X + 6 * X ^ 2) = 24 * X * (1 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 : ℝ) ^ ((2 : ℝ) - n) * ((9 - Real.sqrt 57) ^ n * (3 + Real.sqrt 57) +
        (-3 + Real.sqrt 57) * (9 + Real.sqrt 57) ^ n) / Real.sqrt 57 := by
  sorry

end OMA.S_oeis_a223291
