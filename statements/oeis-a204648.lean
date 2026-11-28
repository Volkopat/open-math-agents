import Mathlib

/-!
# OEIS A204648: Barker's g.f. and closed forms for (n+1) X 6 binary arrays with monotone pair sums

Source: https://oeis.org/A204648 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 17 2012), offset 1: Number of (n+1) X 6 0..1 arrays with column and
row pair sums b(i,j)=a(i,j)+a(i,j-1) and c(i,j)=a(i,j)+a(i-1,j) nondecreasing in column and row
directions, respectively. Column 5 of A204651. Data: 80, 137, 284, 571, 1076, 1918, 3261, ...
Formula: Empirical: a(n) = 6*a(n-1) -14*a(n-2) +14*a(n-3) -14*a(n-5) +14*a(n-6) -6*a(n-7)
+a(n-8) for n>11. Conjectures from Colin Barker, Jun 08 2018: G.f.: x*(80 - 343*x + 582*x^2 -
335*x^3 - 292*x^4 + 600*x^5 - 379*x^6 + 89*x^7 - 4*x^8 + 8*x^9 - 4*x^10) / ((1 - x)^7*(1 + x)).
a(n) = (-10080 + 43776*n + 15308*n^2 + 2970*n^3 + 620*n^4 + 54*n^5 + 2*n^6)/1440 for n>3 and
even. a(n) = (-10890 + 43776*n + 15308*n^2 + 2970*n^3 + 620*n^4 + 54*n^5 + 2*n^6)/1440 for n>3
and odd.

Formalization notes:
* An array is f : Fin (n+1) -> Fin 6 -> Fin 2, with f i j the entry in row i and column j.
  The horizontal pair sums b(i,j) = f(i,j) + f(i,j-1) (j >= 1) are nondecreasing in the column
  direction, b(i,j) <= b(i+1,j); the vertical pair sums c(i,j) = f(i,j) + f(i-1,j) (i >= 1) are
  nondecreasing in the row direction, c(i,j) <= c(i,j+1). This is the reading of the staged
  sibling A204645 (column 2 of A204651); it reproduces the table A204651 in a separate
  brute-force check, and the data below.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x)*D(x) = N(x) in Q[[x]], which is
  equivalent to A = N/D because D has constant term 1.
* The closed forms are stated in Q for n > 3, split by the parity of n, as in the entry.
* `main` is the conjunction of Barker's three conjectures.
* Controls proved in the proof file: a(1..26) = 80, 137, 284, 571, 1076, 1918, 3261, 5329, 8408,
  12867, 19162, 27859, 39640, 55328, 75895, 102489, 136444, 179309, 232860, 299131, 380428,
  479362, 598865, 742225, 913104, 1115575, which include the entry's data (a(1..23)).
-/

namespace OMA.S_oeis_a204648

open PowerSeries Finset

/-- A204648: the number of (n+1) X 6 arrays f with entries 0..1 (f i j in row i, column j) such
that for consecutive rows i, i' = i + 1 and consecutive columns j, j' = j + 1 the horizontal pair
sum b(i, j') = f(i,j') + f(i,j) does not decrease from row i to row i' (column direction) and the
vertical pair sum c(i', j) = f(i',j) + f(i,j) does not decrease from column j to column j' (row
direction). -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 6 → Fin 2)).filter (fun f =>
    ∀ i i' : Fin (n + 1), i'.val = i.val + 1 → ∀ j j' : Fin 6, j'.val = j.val + 1 →
      (f i j').val + (f i j).val ≤ (f i' j').val + (f i' j).val ∧
        (f i' j).val + (f i j).val ≤ (f i' j').val + (f i j').val)).card

/-- Barker's conjectures: the g.f. and the two closed forms. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 7 * (1 + X)) =
      X * (80 - 343 * X + 582 * X ^ 2 - 335 * X ^ 3 - 292 * X ^ 4 + 600 * X ^ 5 - 379 * X ^ 6 +
        89 * X ^ 7 - 4 * X ^ 8 + 8 * X ^ 9 - 4 * X ^ 10) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 0 →
      (a n : ℚ) = (-10080 + 43776 * n + 15308 * n ^ 2 + 2970 * n ^ 3 + 620 * n ^ 4 + 54 * n ^ 5 +
        2 * n ^ 6) / 1440) ∧
    (∀ n : ℕ, 3 < n → n % 2 = 1 →
      (a n : ℚ) = (-10890 + 43776 * n + 15308 * n ^ 2 + 2970 * n ^ 3 + 620 * n ^ 4 + 54 * n ^ 5 +
        2 * n ^ 6) / 1440) := by
  sorry

end OMA.S_oeis_a204648
