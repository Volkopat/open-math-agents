import Mathlib

/-!
# OEIS A204645: Barker's g.f. and closed forms for (n+1) X 3 binary arrays with monotone pair sums

Source: https://oeis.org/A204645 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 17 2012), offset 1: Number of (n+1) X 3 0..1 arrays with column and
row pair sums b(i,j)=a(i,j)+a(i,j-1) and c(i,j)=a(i,j)+a(i-1,j) nondecreasing in column and row
directions, respectively. Column 2 of A204651. Data: 16, 32, 56, 90, 137, 200, 283, ...
Formula: Empirical: a(n) = 4*a(n-1) - 5*a(n-2) + 5*a(n-4) - 4*a(n-5) + a(n-6). Conjectures from
Colin Barker, Jun 08 2018: G.f.: x*(16 - 32*x + 8*x^2 + 26*x^3 - 23*x^4 + 6*x^5) / ((1 - x)^5*
(1 + x)). a(n) = (576 + 704*n + 232*n^2 + 16*n^3 + 2*n^4)/96 for n even.
a(n) = (582 + 704*n + 232*n^2 + 16*n^3 + 2*n^4)/96 for n odd.

Formalization notes:
* An array is f : Fin (n+1) -> Fin 3 -> Fin 2, with f i j the entry in row i and column j.
  The horizontal pair sums b(i,j) = f(i,j) + f(i,j-1) (j = 1, 2) are nondecreasing in the column
  direction, b(i,j) <= b(i+1,j); the vertical pair sums c(i,j) = f(i,j) + f(i-1,j) (i >= 1) are
  nondecreasing in the row direction, c(i,j) <= c(i,j+1). This reading reproduces the table
  A204651 (checked by a separate brute-force program for (n+1) X (k+1) with n, k <= 3, where the
  other reading, b along rows and c along columns, does not) and the data below.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x)*D(x) = N(x) in Q[[x]], which is
  equivalent to A = N/D because D has constant term 1.
* The closed forms are stated in Q for n >= 1 (the entry's offset), split by the parity of n.
* `main` is the conjunction of Barker's three conjectures.
* Controls proved in the proof file: a(1..28) = 16, 32, 56, 90, 137, 200, 283, 390, 526, 696,
  906, 1162, 1471, 1840, 2277, 2790, 3388, 4080, 4876, 5786, 6821, 7992, 9311, 10790, 12442,
  14280, 16318, 18570, the entry's data.
-/

namespace OMA.S_oeis_a204645

open PowerSeries Finset

/-- A204645: the number of (n+1) X 3 arrays f with entries 0..1 (f i j in row i, column j) such
that for consecutive rows i, i' = i + 1 and consecutive columns j, j' = j + 1 the horizontal pair
sum b(i, j') = f(i,j') + f(i,j) does not decrease from row i to row i' (column direction) and the
vertical pair sum c(i', j) = f(i',j) + f(i,j) does not decrease from column j to column j' (row
direction). -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 3 → Fin 2)).filter (fun f =>
    ∀ i i' : Fin (n + 1), i'.val = i.val + 1 → ∀ j j' : Fin 3, j'.val = j.val + 1 →
      (f i j').val + (f i j).val ≤ (f i' j').val + (f i' j).val ∧
        (f i' j).val + (f i j).val ≤ (f i' j').val + (f i j').val)).card

/-- Barker's conjectures: the g.f. and the two closed forms. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X)) =
      X * (16 - 32 * X + 8 * X ^ 2 + 26 * X ^ 3 - 23 * X ^ 4 + 6 * X ^ 5) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 →
      (a n : ℚ) = (576 + 704 * n + 232 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 96) ∧
    (∀ n : ℕ, n % 2 = 1 →
      (a n : ℚ) = (582 + 704 * n + 232 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 96) := by
  sorry

end OMA.S_oeis_a204645
