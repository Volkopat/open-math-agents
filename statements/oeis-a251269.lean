import Mathlib

/-!
# OEIS A251269: Barker's g.f. and closed form for (2+1) X (n+1) binary arrays with no 2 X 2 subblock having x11-x00 less than x10-x01

Source: https://oeis.org/A251269 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A251269 (R. H. Hardin, Dec 01 2014), offset 1: Number of (2+1) X (n+1) 0..1 arrays with no 2 X
2 subblock having x11-x00 less than x10-x01. Row 2 of A251268. Data: 35, 114, 313, 772, 1775, ...
Formula section: Empirical: a recurrence of order 5. Conjectures from Colin Barker, Nov 27 2018:
(Start) G.f.: x*(35-96*x+119*x^2-70*x^3+16*x^4) / ((1-x)^4*(1-2*x)). a(n) =
8*(9*2^n-8)-(109*n)/3-8*n^2-(2*n^3)/3. (End)

Formalization notes:
* An array is a function x : Fin 3 -> Fin (n + 1) -> Fin 2, x i j being the element in row i and
  column j, so a(n) counts arrays with 3 rows and n + 1 columns. The 2 X 2 subblocks are the blocks
  of rows i, i' = i + 1 and columns j, j' = j + 1, and xab is the element in row a and column b of
  the block (x00 top left, x11 bottom right); the differences are taken in Z. This reading
  reproduces the entry's data and the whole table A251268 (brute force over all arrays for small
  sizes, a transfer for the rest). The proof counts the transposed arrays row by row.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal to
  the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed form carries no range in the source; it is stated in Q for every n >=
  1 (the offset).
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..27) = 35, 114, 313, 772, 1775, 3894, 8277, 17224, 35339,
  71834, 145137, 292108, 586471, 1175678, 2354637, 4713168, 9430915, 18867170, 37740521, 75488148,
  150984415, 301978054, 603966533, 1207944792, 2415902715, 4831820074, 9663656417, the entry's data.
-/

namespace OMA.S_oeis_a251269

open PowerSeries

/-- A251269(n): the number of (2+1) X (n+1) arrays x with entries 0..1 (x i j in row i and column j)
with no 2 X 2 subblock, rows i, i' = i + 1 and columns j, j' = j + 1, having x11 - x00 less than x10
- x01, where x00 = x(i,j), x01 = x(i,j'), x10 = x(i',j), x11 = x(i',j'). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 3 → Fin (n + 1) → Fin 2)).filter (fun x =>
    ∀ i i' : Fin 3, i'.val = i.val + 1 → ∀ j j' : Fin (n + 1), j'.val = j.val + 1 →
      ¬ (((x i' j').val : ℤ) - (x i j).val < ((x i' j).val : ℤ) - (x i j').val))).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 4 * (1 - 2 * X)) =
        X * (35 - 96 * X + 119 * X ^ 2 - 70 * X ^ 3 + 16 * X ^ 4) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
          8 * (9 * 2 ^ n - 8) - (109 * n) / 3 - 8 * n ^ 2 - (2 * n ^ 3) / 3 := by
  sorry

end OMA.S_oeis_a251269
