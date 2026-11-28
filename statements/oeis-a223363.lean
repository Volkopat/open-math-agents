import Mathlib

/-!
# OEIS A223363: Barker's g.f. and closed form for n X 1 colorings by the 6 X 6 X 6 triangular graph

Source: https://oeis.org/A223363 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Mar 19 2013), offset 1: 6 X 6 X 6 triangular graph coloring a rectangular
array: number of n X 1 0..20 arrays where 0..20 label nodes of the fully triangulated graph and
every array movement to a horizontal or vertical neighbor moves along an edge of this graph.
Data: 21, 90, 420, 1992, 9552, 45984, ... Formula: Empirical: a(n) = 6*a(n-1) - 4*a(n-2) -
8*a(n-3). Conjectures from Colin Barker, Aug 20 2018: G.f.: 3*x*(7 - 12*x - 12*x^2) /
((1 - 2*x)*(1 - 4*x - 4*x^2)). a(n) = (3/2)*(2^n-(2-2*sqrt(2))^n*(-1+sqrt(2)) +
2^(1/2+n)*(1+sqrt(2))^n + (2*(1+sqrt(2)))^n).

Formalization notes:
* The 6 X 6 X 6 triangular graph is the triangular grid with six nodes on a side: node
  r(r+1)/2 + c is the c-th node of row r (0 <= c <= r <= 5), joined to its right neighbour in its
  row and to the two nodes below it (45 edges). The smaller entries of the family, A223211
  (3 X 3 X 3), A223299 (4 X 4 X 4) and A223337 (5 X 5 X 5), list their edges explicitly; this edge
  list agrees with each of them on its nodes and extends them by the sixth row. The count does not
  depend on the labelling.
* An n X 1 array is a function from the n rows to the labels 0..20; its only neighbours are
  vertical, rows i and i + 1, and a move along an edge means that the two labels are joined by
  one of the listed edges (in either direction).
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1). The identity A(x) = N(x)/D(x) is stated as
  A(x)*D(x) = N(x) in Q[[x]], which is equivalent because D has constant term 1.
* The closed form is stated in the reals for every n >= 1, with 2^(1/2+n) the real power.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..16) = 21, 90, 420, 1992, 9552, 45984, 221760, 1070208,
  5166336, 24943104, 120431616, 581486592, 2807648256, 13556490240, 65456455680, 316051587072,
  the entry's data. The second column of the table A223370 (n X 2 arrays: 90, 990, 11610, 139158,
  ...) was reproduced by a separate program with the same graph.
-/

namespace OMA.S_oeis_a223363

open PowerSeries Finset

/-- The 45 edges of the 6 X 6 X 6 triangular graph on 0..20: node r(r+1)/2 + c is the c-th node
of row r (0 <= c <= r <= 5), joined to its right neighbour in the row and to the two nodes below
it; the list extends the edge lists of A223211, A223299 and A223337. -/
def edges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (2, 4), (3, 4), (2, 5), (4, 5), (3, 6), (3, 7), (4, 7),
    (6, 7), (4, 8), (5, 8), (7, 8), (5, 9), (8, 9), (6, 10), (6, 11), (7, 11), (10, 11), (7, 12),
    (8, 12), (11, 12), (8, 13), (9, 13), (12, 13), (9, 14), (13, 14), (10, 15), (10, 16),
    (11, 16), (15, 16), (11, 17), (12, 17), (16, 17), (12, 18), (13, 18), (17, 18), (13, 19),
    (14, 19), (18, 19), (14, 20), (19, 20)]

/-- Two labels are adjacent when they are joined by an edge of the graph. -/
def adj (x y : Fin 21) : Prop := (x.val, y.val) ∈ edges ∨ (y.val, x.val) ∈ edges

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- A223363: the number of n X 1 arrays f with entries 0..20 in which every move to the vertical
neighbour (row i to row i + 1) is along an edge. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin n → Fin 21)).filter
    (fun f => ∀ i j : Fin n, j.val = i.val + 1 → adj (f i) (f j))).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 2 * X) * (1 - 4 * X - 4 * X ^ 2)) = 3 * X * (7 - 12 * X - 12 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (3 / 2) * (2 ^ n - (2 - 2 * Real.sqrt 2) ^ n * (-1 + Real.sqrt 2) +
        (2 : ℝ) ^ ((1 : ℝ) / 2 + n) * (1 + Real.sqrt 2) ^ n + (2 * (1 + Real.sqrt 2)) ^ n) := by
  sorry

end OMA.S_oeis_a223363
