import Mathlib

/-!
# OEIS A251270: Barker's g.f. and closed form for (3+1) X (n+1) binary arrays with no 2 X 2 subblock having x11-x00 less than x10-x01

Source: https://oeis.org/A251270 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A251270 (R. H. Hardin, Dec 01 2014), offset 1: Number of (3+1) X (n+1) 0..1 arrays with no 2 X
2 subblock having x11-x00 less than x10-x01. Row 3 of A251268. Data: 108, 480, 1667, 4930, 13052,
... Formula section: Empirical: a(n) = 9*a(n-1) - 35*a(n-2) + 77*a(n-3) - 105*a(n-4) + 91*a(n-5) -
49*a(n-6) + 15*a(n-7) - 2*a(n-8). Conjectures from Colin Barker, Nov 27 2018: (Start) G.f.: x*(108 -
492*x + 1127*x^2 - 1589*x^3 + 1407*x^4 - 769*x^5 + 238*x^6 - 32*x^7) / ((1 - x)^7*(1 - 2*x)). a(n) =
(5760*(25*2^(1 + n)-49) - 186828*n - 57236*n^2 - 9885*n^3 - 905*n^4 - 27*n^5 + n^6) / 360. (End)

Formalization notes:
* An array is a function x : Fin 4 -> Fin (n + 1) -> Fin 2, x i j being the element in row i and
  column j, so a(n) counts arrays with 4 rows and n + 1 columns. The 2 X 2 subblocks are the blocks
  of rows i, i' = i + 1 and columns j, j' = j + 1, and xab is the element in row a and column b of
  the block (x00 top left, x11 bottom right); the differences are taken in Z. This reading
  reproduces the entry's data and the whole table A251268 (brute force over all arrays for small
  sizes, a transfer for the rest). The proof counts the transposed arrays row by row.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal to
  the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed form carries no range in the source; it is stated in Q for every n >=
  1 (the offset).
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..24) = 108, 480, 1667, 4930, 13052, 31936, 73805, 163604,
  351804, 740008, 1532159, 3136950, 6372636, 12876648, 25924809, 52069752, 104417740, 209182288,
  418791387, 838101930, 1676828540, 3354401200, 6709680485, 13420387996, the entry's data.
-/

namespace OMA.S_oeis_a251270

open PowerSeries

/-- A251270(n): the number of (3+1) X (n+1) arrays x with entries 0..1 (x i j in row i and column j)
with no 2 X 2 subblock, rows i, i' = i + 1 and columns j, j' = j + 1, having x11 - x00 less than x10
- x01, where x00 = x(i,j), x01 = x(i,j'), x10 = x(i',j), x11 = x(i',j'). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 4 → Fin (n + 1) → Fin 2)).filter (fun x =>
    ∀ i i' : Fin 4, i'.val = i.val + 1 → ∀ j j' : Fin (n + 1), j'.val = j.val + 1 →
      ¬ (((x i' j').val : ℤ) - (x i j).val < ((x i' j).val : ℤ) - (x i j').val))).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 7 * (1 - 2 * X)) =
        X * (108 - 492 * X + 1127 * X ^ 2 - 1589 * X ^ 3 + 1407 * X ^ 4 - 769 * X ^ 5 + 238 * X ^ 6 -
          32 * X ^ 7) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
          (5760 * (25 * 2 ^ (1 + n) - 49) - 186828 * n - 57236 * n ^ 2 - 9885 * n ^ 3 - 905 * n ^ 4 -
            27 * n ^ 5 + n ^ 6) / 360 := by
  sorry

end OMA.S_oeis_a251270
