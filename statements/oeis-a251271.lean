import Mathlib

/-!
# OEIS A251271: Barker's g.f. and closed form for (4+1) X (n+1) binary arrays with no 2 X 2 subblock having x11-x00 less than x10-x01

Source: https://oeis.org/A251271 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A251271 (R. H. Hardin, Dec 01 2014), offset 1: Number of (4+1) X (n+1) 0..1 arrays with no 2 X
2 subblock having x11-x00 less than x10-x01. Row 4 of A251268. Data: 337, 2058, 9109, 32636, 100843,
... Formula section: Empirical: a(n) = 11*a(n-1) - 54*a(n-2) + 156*a(n-3) - 294*a(n-4) + 378*a(n-5)
- 336*a(n-6) + 204*a(n-7) - 81*a(n-8) + 19*a(n-9) - 2*a(n-10). Conjectures from Colin Barker, Nov 27
2018: (Start) G.f.: x*(337 - 1649*x + 4669*x^2 - 9003*x^3 + 11763*x^4 - 10549*x^5 + 6447*x^6 -
2573*x^7 + 606*x^8 - 64*x^9) / ((1 - x)^9*(1 - 2*x)). a(n) = (20160*(1369*2^n-1365) - 18907464*n -
6363848*n^2 - 1352064*n^3 - 190036*n^4 - 16401*n^5 - 637*n^6 + 9*n^7 + n^8) / 2520. (End)

Formalization notes:
* An array is a function x : Fin 5 -> Fin (n + 1) -> Fin 2, x i j being the element in row i and
  column j, so a(n) counts arrays with 5 rows and n + 1 columns. The 2 X 2 subblocks are the blocks
  of rows i, i' = i + 1 and columns j, j' = j + 1, and xab is the element in row a and column b of
  the block (x00 top left, x11 bottom right); the differences are taken in Z. This reading
  reproduces the entry's data and the whole table A251268 (brute force over all arrays for small
  sizes, a transfer for the rest). The proof counts the transposed arrays row by row.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal to
  the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed form carries no range in the source; it is stated in Q for every n >=
  1 (the offset).
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..23) = 337, 2058, 9109, 32636, 100843, 279718, 715685,
  1722176, 3954037, 8757506, 18871133, 39828260, 82762159, 170015870, 346360653, 701430696,
  1414589161, 2844655514, 5709353797, 11444200908, 22920272755, 45879723734, 91806810133, the
  entry's data.
-/

namespace OMA.S_oeis_a251271

open PowerSeries

/-- A251271(n): the number of (4+1) X (n+1) arrays x with entries 0..1 (x i j in row i and column j)
with no 2 X 2 subblock, rows i, i' = i + 1 and columns j, j' = j + 1, having x11 - x00 less than x10
- x01, where x00 = x(i,j), x01 = x(i,j'), x10 = x(i',j), x11 = x(i',j'). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 5 → Fin (n + 1) → Fin 2)).filter (fun x =>
    ∀ i i' : Fin 5, i'.val = i.val + 1 → ∀ j j' : Fin (n + 1), j'.val = j.val + 1 →
      ¬ (((x i' j').val : ℤ) - (x i j).val < ((x i' j).val : ℤ) - (x i j').val))).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 9 * (1 - 2 * X)) =
        X * (337 - 1649 * X + 4669 * X ^ 2 - 9003 * X ^ 3 + 11763 * X ^ 4 - 10549 * X ^ 5 +
          6447 * X ^ 6 - 2573 * X ^ 7 + 606 * X ^ 8 - 64 * X ^ 9) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
          (20160 * (1369 * 2 ^ n - 1365) - 18907464 * n - 6363848 * n ^ 2 - 1352064 * n ^ 3 -
            190036 * n ^ 4 - 16401 * n ^ 5 - 637 * n ^ 6 + 9 * n ^ 7 + n ^ 8) / 2520 := by
  sorry

end OMA.S_oeis_a251271
