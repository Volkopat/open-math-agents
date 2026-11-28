import Mathlib

/-!
# OEIS A204646: Barker's g.f. and closed forms for (n+1) X 4 binary arrays with monotone pair sums

Source: https://oeis.org/A204646 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 17 2012), offset 1: Number of (n+1) X 4 0..1 arrays with column and
row pair sums b(i,j)=a(i,j)+a(i,j-1) and c(i,j)=a(i,j)+a(i-1,j) nondecreasing in column and row
directions, respectively. Column 3 of A204651. Data: 28, 56, 104, 178, 284, 434, 637, ...
Formula: Empirical: a(n) = 4*a(n-1) -5*a(n-2) +5*a(n-4) -4*a(n-5) +a(n-6) for n>7. Conjectures
from Colin Barker, Jun 08 2018: G.f.: x*(28 - 56*x + 20*x^2 + 42*x^3 - 48*x^4 + 20*x^5 - 3*x^6) /
((1 - x)^5*(1 + x)). a(n) = (256 + 400*n + 144*n^2 + 16*n^3 + 2*n^4)/32 for n>1 and even.
a(n) = (238 + 400*n + 144*n^2 + 16*n^3 + 2*n^4)/32 for n>1 and odd.

Formalization notes:
* An array is f : Fin (n+1) -> Fin 4 -> Fin 2, with f i j the entry in row i and column j.
  The horizontal pair sums b(i,j) = f(i,j) + f(i,j-1) (j >= 1) are nondecreasing in the column
  direction, b(i,j) <= b(i+1,j); the vertical pair sums c(i,j) = f(i,j) + f(i-1,j) (i >= 1) are
  nondecreasing in the row direction, c(i,j) <= c(i,j+1). This is the reading of the staged
  sibling A204645 (column 2 of A204651); it reproduces the table A204651 in a separate
  brute-force check, and the data below.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x)*D(x) = N(x) in Q[[x]], which is
  equivalent to A = N/D because D has constant term 1.
* The closed forms are stated in Q for n > 1, split by the parity of n, as in the entry.
* `main` is the conjunction of Barker's three conjectures.
* Controls proved in the proof file: a(1..26) = 28, 56, 104, 178, 284, 434, 637, 908, 1259, 1708,
  2270, 2966, 3814, 4838, 6059, 7504, 9197, 11168, 13444, 16058, 19040, 22426, 26249, 30548,
  35359, 40724, the entry's data.
-/

namespace OMA.S_oeis_a204646

open PowerSeries Finset

/-- A204646: the number of (n+1) X 4 arrays f with entries 0..1 (f i j in row i, column j) such
that for consecutive rows i, i' = i + 1 and consecutive columns j, j' = j + 1 the horizontal pair
sum b(i, j') = f(i,j') + f(i,j) does not decrease from row i to row i' (column direction) and the
vertical pair sum c(i', j) = f(i',j) + f(i,j) does not decrease from column j to column j' (row
direction). -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 4 → Fin 2)).filter (fun f =>
    ∀ i i' : Fin (n + 1), i'.val = i.val + 1 → ∀ j j' : Fin 4, j'.val = j.val + 1 →
      (f i j').val + (f i j).val ≤ (f i' j').val + (f i' j).val ∧
        (f i' j).val + (f i j).val ≤ (f i' j').val + (f i j').val)).card

/-- Barker's conjectures: the g.f. and the two closed forms. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X)) =
      X * (28 - 56 * X + 20 * X ^ 2 + 42 * X ^ 3 - 48 * X ^ 4 + 20 * X ^ 5 - 3 * X ^ 6) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 →
      (a n : ℚ) = (256 + 400 * n + 144 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 32) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 →
      (a n : ℚ) = (238 + 400 * n + 144 * n ^ 2 + 16 * n ^ 3 + 2 * n ^ 4) / 32) := by
  sorry

end OMA.S_oeis_a204646
