import Mathlib

/-!
# OEIS A207142: Barker's g.f. and closed forms for (n+1) X 2 0..2 arrays whose 2 X 2 subblocks are invertible and commute with their neighbors

Source: https://oeis.org/A207142 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A207142 (R. H. Hardin, Feb 15 2012), offset 1: Number of (n+1) X 2 0..2 arrays with every 2 X
2 subblock having nonzero determinant and commuting with every horizontal or vertical neighbor.
Column 1 of A207149. Data: 50, 30, 80, 62, 159, 122, ... Formula section: Empirical recurrence.
Conjectures from Colin Barker, Jun 19 2018: (Start) G.f.: x*(50 - 20*x - 50*x^2 + 22*x^3 - 3*x^4 -
x^5 - x^6 + x^7) / ((1 - x)*(1 - 2*x^2)). a(n) = 15 * 2^(n/2) + 2 for n>5 and even. a(n) = 313 *
2^((n-7)/2) + 2 for n>5 and odd. (End)

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 2 -> Fin 3, x i j being the element in row i and
  column j. A 2 X 2 subblock is read as the integer matrix !![x(i,j), x(i,j'); x(i',j), x(i',j')]
  for i' = i + 1, j' = j + 1; its determinant is x(i,j) x(i',j') - x(i,j') x(i',j), and commuting
  means equal products in both orders (matrix multiplication in Mathlib). With two columns every
  block has only vertical neighbors, the blocks one row up or down; commuting is symmetric, so the
  condition is stated for each block and the block below it. This reading reproduces the entry's
  data and the table A207149 (brute force over all arrays for small sizes, a transfer on pairs of
  rows for the rest).
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal to
  the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed forms are stated in the reals with the exponents as in the source,
  real powers (Real.rpow) of real exponents; for the n of each form the exponents are natural
  numbers.
* `main` is the conjunction of Barker's three statements.
* Controls proved in the proof file: a(1..37) = 50, 30, 80, 62, 159, 122, 315, 242, 628, 482, 1254,
  962, 2506, 1922, 5010, 3842, 10018, 7682, 20034, 15362, 40066, 30722, 80130, 61442, 160258,
  122882, 320514, 245762, 641026, 491522, 1282050, 983042, 2564098, 1966082, 5128194, 3932162,
  10256386, the entry's data.
-/

namespace OMA.S_oeis_a207142

open PowerSeries

/-- A207142(n): the number of (n+1) X 2 arrays x with entries 0..2 (x i j in row i and column j) in
which every 2 X 2 subblock, rows i, i + 1 and columns j, j + 1, read as the integer matrix [[x(i,j),
x(i,j+1)], [x(i+1,j), x(i+1,j+1)]], has nonzero determinant and commutes with its vertical neighbor,
the block of rows i + 1, i + 2 (with two columns no block has a horizontal neighbor). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 2 → Fin 3)).filter (fun x =>
    (∀ i i' : Fin (n + 1), i'.val = i.val + 1 →
      (∀ j j' : Fin 2, j'.val = j.val + 1 → (((x i j).val : ℤ) * ((x i' j').val : ℤ) - ((x i j').val : ℤ) * ((x i' j).val : ℤ) ≠ 0))) ∧
    ∀ i i' i'' : Fin (n + 1), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      (∀ j j' : Fin 2, j'.val = j.val + 1 → (!![((x i j).val : ℤ), ((x i j').val : ℤ); ((x i' j).val : ℤ), ((x i' j').val : ℤ)] * !![((x i' j).val : ℤ), ((x i' j').val : ℤ); ((x i'' j).val : ℤ), ((x i'' j').val : ℤ)] =
              !![((x i' j).val : ℤ), ((x i' j').val : ℤ); ((x i'' j).val : ℤ), ((x i'' j').val : ℤ)] * !![((x i j).val : ℤ), ((x i j').val : ℤ); ((x i' j).val : ℤ), ((x i' j').val : ℤ)])))).card

/-- Barker's conjectures: the g.f. and the two closed forms. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X ^ 2)) =
        X * (50 - 20 * X - 50 * X ^ 2 + 22 * X ^ 3 - 3 * X ^ 4 - X ^ 5 - X ^ 6 + X ^ 7) ∧
      (∀ n : ℕ, 5 < n → n % 2 = 0 → (a n : ℝ) = 15 * (2 : ℝ) ^ ((n : ℝ) / 2) + 2) ∧
      (∀ n : ℕ, 5 < n → n % 2 = 1 → (a n : ℝ) = 313 * (2 : ℝ) ^ (((n : ℝ) - 7) / 2) + 2) := by
  sorry

end OMA.S_oeis_a207142
