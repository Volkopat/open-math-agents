import Mathlib

/-!
# OEIS A204647: Barker's g.f. and closed forms for (n+1) X 5 binary arrays with monotone pair sums

Source: https://oeis.org/A204647 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 17 2012), offset 1: Number of (n+1) X 5 0..1 arrays with column and
row pair sums b(i,j)=a(i,j)+a(i,j-1) and c(i,j)=a(i,j)+a(i-1,j) nondecreasing in column and row
directions, respectively. Column 4 of A204651. Data: 48, 90, 178, 330, 571, 938, 1478, ...
Formula: Empirical: a(n) = 5*a(n-1) -9*a(n-2) +5*a(n-3) +5*a(n-4) -9*a(n-5) +5*a(n-6) -a(n-7)
for n>9. Conjectures from Colin Barker, Jun 08 2018: G.f.: x*(48 - 150*x + 160*x^2 + 10*x^3 -
167*x^4 + 145*x^5 - 43*x^6 - 5*x^7 + 4*x^8) / ((1 - x)^6*(1 + x)).
a(n) = (1920 + 9776*n + 3480*n^2 + 540*n^3 + 90*n^4 + 4*n^5)/480 for n>2 and even.
a(n) = (1950 + 9776*n + 3480*n^2 + 540*n^3 + 90*n^4 + 4*n^5)/480 for n>2 and odd.

Formalization notes:
* An array is f : Fin (n+1) -> Fin 5 -> Fin 2, with f i j the entry in row i and column j.
  The horizontal pair sums b(i,j) = f(i,j) + f(i,j-1) (j >= 1) are nondecreasing in the column
  direction, b(i,j) <= b(i+1,j); the vertical pair sums c(i,j) = f(i,j) + f(i-1,j) (i >= 1) are
  nondecreasing in the row direction, c(i,j) <= c(i,j+1). This is the reading of the staged
  sibling A204645 (column 2 of A204651); it reproduces the table A204651 in a separate
  brute-force check, and the data below.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x)*D(x) = N(x) in Q[[x]], which is
  equivalent to A = N/D because D has constant term 1.
* The closed forms are stated in Q for n > 2, split by the parity of n, as in the entry.
* `main` is the conjunction of Barker's three conjectures.
* Controls proved in the proof file: a(1..26) = 48, 90, 178, 330, 571, 938, 1478, 2248, 3317,
  4766, 6690, 9198, 12415, 16482, 21558, 27820, 35465, 44710, 55794, 68978, 84547, 102810, 124102,
  148784, 177245, 209902, which include the entry's data (a(1..24)).
-/

namespace OMA.S_oeis_a204647

open PowerSeries Finset

/-- A204647: the number of (n+1) X 5 arrays f with entries 0..1 (f i j in row i, column j) such
that for consecutive rows i, i' = i + 1 and consecutive columns j, j' = j + 1 the horizontal pair
sum b(i, j') = f(i,j') + f(i,j) does not decrease from row i to row i' (column direction) and the
vertical pair sum c(i', j) = f(i',j) + f(i,j) does not decrease from column j to column j' (row
direction). -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 5 → Fin 2)).filter (fun f =>
    ∀ i i' : Fin (n + 1), i'.val = i.val + 1 → ∀ j j' : Fin 5, j'.val = j.val + 1 →
      (f i j').val + (f i j).val ≤ (f i' j').val + (f i' j).val ∧
        (f i' j).val + (f i j).val ≤ (f i' j').val + (f i j').val)).card

/-- Barker's conjectures: the g.f. and the two closed forms. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X)) =
      X * (48 - 150 * X + 160 * X ^ 2 + 10 * X ^ 3 - 167 * X ^ 4 + 145 * X ^ 5 - 43 * X ^ 6 -
        5 * X ^ 7 + 4 * X ^ 8) ∧
    (∀ n : ℕ, 2 < n → n % 2 = 0 →
      (a n : ℚ) = (1920 + 9776 * n + 3480 * n ^ 2 + 540 * n ^ 3 + 90 * n ^ 4 + 4 * n ^ 5) / 480) ∧
    (∀ n : ℕ, 2 < n → n % 2 = 1 →
      (a n : ℚ) = (1950 + 9776 * n + 3480 * n ^ 2 + 540 * n ^ 3 + 90 * n ^ 4 + 4 * n ^ 5) / 480) := by
  sorry

end OMA.S_oeis_a204647
