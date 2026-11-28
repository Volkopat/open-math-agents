import Mathlib

/-!
# OEIS A206261: Barker's g.f. and closed forms for (n+1) X 3 binary arrays whose 2 X 2 subblocks all have the edge increase count of their neighbors

Source: https://oeis.org/A206261 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A206261 (R. H. Hardin, Feb 05 2012), offset 1: Number of (n+1) X 3 0..1 arrays with the number
of rightwards and downwards edge increases in each 2 X 2 subblock equal to the number in all its
horizontal and vertical neighbors. Column 2 of A206267. Data: 24, 28, 44, 64, 93, ... Formula
section: Empirical recurrence. Conjectures from Colin Barker, Jun 14 2018: (Start) G.f.: x*(24 -
44*x + 8*x^2 + 36*x^3 - 27*x^4 + 5*x^5) / ((1 - x)^4*(1 + x)). a(n) = (72 + 26*n + 9*n^2 + n^3) / 6
for n>1 and even. a(n) = (78 + 26*n + 9*n^2 + n^3) / 6 for n>1 and odd. (End)

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 3 -> Fin 2, x i j being the element in row i and
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
* Controls proved in the proof file: a(1..44) = 24, 28, 44, 64, 93, 128, 174, 228, 295, 372, 464,
  568, 689, 824, 978, 1148, 1339, 1548, 1780, 2032, 2309, 2608, 2934, 3284, 3663, 4068, 4504, 4968,
  5465, 5992, 6554, 7148, 7779, 8444, 9148, 9888, 10669, 11488, 12350, 13252, 14199, 15188, 16224,
  17304, the entry's data.
-/

namespace OMA.S_oeis_a206261

open PowerSeries

/-- The number of rightwards and downwards edge increases of the 2 X 2 block with top row (p, q)
and bottom row (r, s): the edges p -> q, r -> s (rightwards) and p -> r, q -> s (downwards). -/
def incr (p q r s : Fin 2) : ℕ :=
  (if p < q then 1 else 0) + (if r < s then 1 else 0) + (if p < r then 1 else 0) +
    (if q < s then 1 else 0)

/-- A206261(n): the number of (n+1) X 3 arrays x with entries 0..1 (x i j in row i and column j) in
which the number of rightwards and downwards edge increases (`incr`) of each 2 X 2 subblock, rows i,
i + 1 and columns j, j + 1, equals that of its horizontal neighbor (columns j + 1, j + 2) and of its
vertical neighbor (rows i + 1, i + 2), hence of all its horizontal and vertical neighbors. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 3 → Fin 2)).filter (fun x =>
    (∀ i i' : Fin (n + 1), i'.val = i.val + 1 →
      (∀ j j' j'' : Fin 3, j'.val = j.val + 1 → j''.val = j'.val + 1 → incr (x i j) (x i j') (x i' j) (x i' j') = incr (x i j') (x i j'') (x i' j') (x i' j''))) ∧
    ∀ i i' i'' : Fin (n + 1), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      (∀ j j' : Fin 3, j'.val = j.val + 1 → incr (x i j) (x i j') (x i' j) (x i' j') = incr (x i' j) (x i' j') (x i'' j) (x i'' j')))).card

/-- Barker's conjectures: the g.f. and the two closed forms for n > 1. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 4 * (1 + X)) =
        X * (24 - 44 * X + 8 * X ^ 2 + 36 * X ^ 3 - 27 * X ^ 4 + 5 * X ^ 5) ∧
      (∀ n : ℕ, 1 < n → n % 2 = 0 → (a n : ℚ) = (72 + 26 * n + 9 * n ^ 2 + n ^ 3) / 6) ∧
      (∀ n : ℕ, 1 < n → n % 2 = 1 → (a n : ℚ) = (78 + 26 * n + 9 * n ^ 2 + n ^ 3) / 6) := by
  sorry

end OMA.S_oeis_a206261
