import Mathlib

/-!
# OEIS A206336: Barker's g.f. and closed forms for (n+1) X 2 0..3 arrays whose 2 X 2 subblocks are invertible and commute with their neighbors

Source: https://oeis.org/A206336 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A206336 (R. H. Hardin, Feb 06 2012), offset 1: Number of (n+1) X 2 0..3 arrays with every 2 X
2 subblock having nonzero determinant and commuting with every horizontal or vertical neighbor.
Column 1 of A206343. Data: 192, 96, 455, 296, 1376, 880, ... Formula section: Empirical recurrence.
Conjectures from Colin Barker, Jun 15 2018: (Start) G.f.: x*(192 - 96*x - 217*x^2 + 129*x^3 + 3*x^4
- 19*x^5 - 9*x^6 - x^7 + 4*x^8 + 2*x^9) / ((1 - x)*(1 - 3*x^2)). a(n) = 872 * 3^((n-9)/2+3/2) + 6
for n>7 and even. a(n) = 12313 * 3^((n-9)/2) + 6 for n>7 and odd. (End)

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 2 -> Fin 4, x i j being the element in row i and
  column j. A 2 X 2 subblock is read as the integer matrix !![x(i,j), x(i,j'); x(i',j), x(i',j')]
  for i' = i + 1, j' = j + 1; its determinant is x(i,j) x(i',j') - x(i,j') x(i',j), and commuting
  means equal products in both orders (matrix multiplication in Mathlib). With two columns every
  block has only vertical neighbors, the blocks one row up or down; commuting is symmetric, so the
  condition is stated for each block and the block below it. This reading reproduces the entry's
  data and the table A206343 (brute force over all arrays for small sizes, a transfer on pairs of
  rows for the rest).
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal to
  the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed forms are stated in the reals with the exponents as in the source,
  real powers (Real.rpow) of real exponents; for the n of each form the exponents are natural
  numbers.
* `main` is the conjunction of Barker's three statements.
* Controls proved in the proof file: a(1..20) = 192, 96, 455, 296, 1376, 880, 4111, 2622, 12319,
  7854, 36945, 23550, 110823, 70638, 332457, 211902, 997359, 635694, 2992065, 1907070, the first 20
  of the entry's 30 listed terms.
-/

namespace OMA.S_oeis_a206336

open PowerSeries

/-- A206336(n): the number of (n+1) X 2 arrays x with entries 0..3 (x i j in row i and column j) in
which every 2 X 2 subblock, rows i, i + 1 and columns j, j + 1, read as the integer matrix [[x(i,j),
x(i,j+1)], [x(i+1,j), x(i+1,j+1)]], has nonzero determinant and commutes with its vertical neighbor,
the block of rows i + 1, i + 2 (with two columns no block has a horizontal neighbor). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter (fun x =>
    (∀ i i' : Fin (n + 1), i'.val = i.val + 1 →
      (∀ j j' : Fin 2, j'.val = j.val + 1 → (((x i j).val : ℤ) * ((x i' j').val : ℤ) - ((x i j').val : ℤ) * ((x i' j).val : ℤ) ≠ 0))) ∧
    ∀ i i' i'' : Fin (n + 1), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      (∀ j j' : Fin 2, j'.val = j.val + 1 → (!![((x i j).val : ℤ), ((x i j').val : ℤ); ((x i' j).val : ℤ), ((x i' j').val : ℤ)] * !![((x i' j).val : ℤ), ((x i' j').val : ℤ); ((x i'' j).val : ℤ), ((x i'' j').val : ℤ)] =
              !![((x i' j).val : ℤ), ((x i' j').val : ℤ); ((x i'' j).val : ℤ), ((x i'' j').val : ℤ)] * !![((x i j).val : ℤ), ((x i j').val : ℤ); ((x i' j).val : ℤ), ((x i' j').val : ℤ)])))).card

/-- Barker's conjectures: the g.f. and the two closed forms. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 3 * X ^ 2)) =
        X * (192 - 96 * X - 217 * X ^ 2 + 129 * X ^ 3 + 3 * X ^ 4 - 19 * X ^ 5 - 9 * X ^ 6 - X ^ 7 +
            4 * X ^ 8 + 2 * X ^ 9) ∧
      (∀ n : ℕ, 7 < n → n % 2 = 0 → (a n : ℝ) =
          872 * (3 : ℝ) ^ (((n : ℝ) - 9) / 2 + 3 / 2) + 6) ∧
      (∀ n : ℕ, 7 < n → n % 2 = 1 → (a n : ℝ) = 12313 * (3 : ℝ) ^ (((n : ℝ) - 9) / 2) + 6) := by
  sorry

end OMA.S_oeis_a206336
