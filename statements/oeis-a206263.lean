import Mathlib

/-!
# OEIS A206263: Barker's g.f. and closed forms for (n+1) X 5 binary arrays whose 2 X 2 subblocks all have the edge increase count of their neighbors

Source: https://oeis.org/A206263 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A206263 (R. H. Hardin, Feb 05 2012), offset 1: Number of (n+1) X 5 0..1 arrays with the number
of rightwards and downwards edge increases in each 2 X 2 subblock equal to the number in all its
horizontal and vertical neighbors. Column 4 of A206267. Data: 50, 64, 135, 260, 471, ... Formula
section: Empirical recurrence. Conjectures from Colin Barker, Jun 15 2018: (Start) G.f.: x*(50 -
186*x + 265*x^2 - 89*x^3 - 184*x^4 + 240*x^5 - 114*x^6 + 20*x^7) / ((1 - x)^6*(1 + x)). a(n) = (1680
+ 1044*n + 580*n^2 + 155*n^3 + 20*n^4 + n^5) / 120 for n>1 and even. a(n) = (1800 + 1044*n + 580*n^2
+ 155*n^3 + 20*n^4 + n^5) / 120 for n>1 and odd. (End)

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 5 -> Fin 2, x i j being the element in row i and
  column j. The 2 X 2 subblocks are the blocks of rows i, i' = i + 1 and columns j, j' = j + 1;
  their rightwards edges are x(i,j) -> x(i,j') and x(i',j) -> x(i',j'), their downwards edges x(i,j)
  -> x(i',j) and x(i,j') -> x(i',j'), and an increase is an edge whose end is larger than its start
  (`incr` counts them). The horizontal neighbors of a block are the blocks one column to the left or
  right and its vertical neighbors those one row up or down; equality with all of them is stated as
  equality between every block and its right neighbor and between every block and the block below
  (the relation is symmetric). This reading reproduces the entry's data and the table A206267 (brute
  force over all arrays for small sizes, a transfer on pairs of rows for the rest).
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal to
  the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed forms are stated in Q for n > 1 with the parity given in the source.
* `main` is the conjunction of Barker's three statements.
* Controls proved in the proof file: a(1..36) = 50, 64, 135, 260, 471, 800, 1296, 2010, 3012, 4376,
  6197, 8576, 11637, 15512, 20358, 26342, 33658, 42512, 53139, 65788, 80739, 98288, 118764, 142514,
  169920, 201384, 237345, 278264, 324641, 377000, 435906, 501950, 575766, 658016, 749407, 850676,
  the entry's data.
-/

namespace OMA.S_oeis_a206263

open PowerSeries

/-- The number of rightwards and downwards edge increases of the 2 X 2 block with top row (p, q)
and bottom row (r, s): the edges p -> q, r -> s (rightwards) and p -> r, q -> s (downwards). -/
def incr (p q r s : Fin 2) : ℕ :=
  (if p < q then 1 else 0) + (if r < s then 1 else 0) + (if p < r then 1 else 0) +
    (if q < s then 1 else 0)

/-- A206263(n): the number of (n+1) X 5 arrays x with entries 0..1 (x i j in row i and column j) in
which the number of rightwards and downwards edge increases (`incr`) of each 2 X 2 subblock, rows i,
i + 1 and columns j, j + 1, equals that of its horizontal neighbor (columns j + 1, j + 2) and of its
vertical neighbor (rows i + 1, i + 2), hence of all its horizontal and vertical neighbors. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 5 → Fin 2)).filter (fun x =>
    (∀ i i' : Fin (n + 1), i'.val = i.val + 1 →
      (∀ j j' j'' : Fin 5, j'.val = j.val + 1 → j''.val = j'.val + 1 → incr (x i j) (x i j') (x i' j) (x i' j') = incr (x i j') (x i j'') (x i' j') (x i' j''))) ∧
    ∀ i i' i'' : Fin (n + 1), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      (∀ j j' : Fin 5, j'.val = j.val + 1 → incr (x i j) (x i j') (x i' j) (x i' j') = incr (x i' j) (x i' j') (x i'' j) (x i'' j')))).card

/-- Barker's conjectures: the g.f. and the two closed forms for n > 1. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 6 * (1 + X)) =
        X * (50 - 186 * X + 265 * X ^ 2 - 89 * X ^ 3 - 184 * X ^ 4 + 240 * X ^ 5 - 114 * X ^ 6 +
            20 * X ^ 7) ∧
      (∀ n : ℕ, 1 < n → n % 2 = 0 → (a n : ℚ) = (1680 + 1044 * n + 580 * n ^ 2 + 155 * n ^ 3 + 20 * n ^ 4 + n ^ 5) / 120) ∧
      (∀ n : ℕ, 1 < n → n % 2 = 1 → (a n : ℚ) = (1800 + 1044 * n + 580 * n ^ 2 + 155 * n ^ 3 + 20 * n ^ 4 + n ^ 5) / 120) := by
  sorry

end OMA.S_oeis_a206263
