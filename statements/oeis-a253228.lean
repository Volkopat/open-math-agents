import Mathlib

/-!
# OEIS A253228: Barker's g.f. and closed form for (n+1) X 6 binary arrays with 2 X 2 diagonal minus antidiagonal minima nondecreasing horizontally and maxima vertically

Source: https://oeis.org/A253228 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A253228 (R. H. Hardin, Dec 29 2014), offset 1: Number of (n+1) X (5+1) 0..1 arrays with every
2 X 2 subblock diagonal minimum minus antidiagonal minimum nondecreasing horizontally and diagonal
maximum minus antidiagonal maximum nondecreasing vertically. Column 5 of A253231. Data: 907, 1775,
1709, 2543, 3936, ... Formula section: Empirical recurrence. Conjectures from Colin Barker, Dec 10
2018: (Start) G.f.: x*(907 - 2760*x + 997*x^2 + 3624*x^3 - 4009*x^4 + 1208*x^5 - 7*x^6 + x^7) / ((1
- x)^3*(1 - 2*x)). a(n) = (3/32)*(5280 + 697*2^n + 1840*n + 208*n^2) for n>4. (End)

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 6 -> Fin 2, x i j being the element in row i and
  column j. For the 2 X 2 subblock B(i,j) with rows i, i' = i + 1 and columns j, j' = j + 1 the
  diagonal is x(i,j), x(i',j') and the antidiagonal x(i,j'), x(i',j). Nondecreasing horizontally
  compares each block with its right neighbor B(i,j') (j'' = j' + 1 below), nondecreasing vertically
  compares it with the block below, B(i',j) (i'' = i' + 1); differences are taken in Z. This reading
  reproduces the entry's data and the table A253231 (brute force over all arrays for small sizes, a
  transfer on pairs of rows for the rest).
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal to
  the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed form is stated in Q for n > 4, the range given in the source; 2^(n-6)
  is an integer power (zpow), so its value at n = 5 is 1/2.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..26) = 907, 1775, 1709, 2543, 3936, 6414, 11022, 19851,
  37083, 71082, 138576, 273021, 541329, 1077324, 2148654, 4290615, 8573799, 17139390, 34269756,
  68529633, 137048493, 274085280, 548157882, 1096302075, 2192589411, 4385162994, the entry's data.
-/

namespace OMA.S_oeis_a253228

open PowerSeries

/-- A253228(n): the number of (n+1) X 6 arrays x with entries 0..1 (x i j in row i and column j) in
which, for the 2 X 2 subblocks B(i,j) with rows i, i + 1 and columns j, j + 1, the diagonal minimum
minus the antidiagonal minimum, min(x(i,j), x(i+1,j+1)) - min(x(i,j+1), x(i+1,j)), is nondecreasing
horizontally (from B(i,j) to B(i,j+1)) and the diagonal maximum minus the antidiagonal maximum is
nondecreasing vertically (from B(i,j) to B(i+1,j)). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 6 → Fin 2)).filter (fun x =>
    (∀ i i' : Fin (n + 1), i'.val = i.val + 1 →
      (∀ j j' j'' : Fin 6, j'.val = j.val + 1 → j''.val = j'.val + 1 → (min ((x i j).val : ℤ) ((x i' j').val : ℤ) - min ((x i j').val : ℤ) ((x i' j).val : ℤ) ≤
              min ((x i j').val : ℤ) ((x i' j'').val : ℤ) - min ((x i j'').val : ℤ) ((x i' j').val : ℤ)))) ∧
    ∀ i i' i'' : Fin (n + 1), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      (∀ j j' : Fin 6, j'.val = j.val + 1 → (max ((x i j).val : ℤ) ((x i' j').val : ℤ) - max ((x i j').val : ℤ) ((x i' j).val : ℤ) ≤
              max ((x i' j).val : ℤ) ((x i'' j').val : ℤ) - max ((x i' j').val : ℤ) ((x i'' j).val : ℤ))))).card

/-- Barker's conjectures: the g.f. and the closed form for n > 4. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 - 2 * X)) =
        X * (907 - 2760 * X + 997 * X ^ 2 + 3624 * X ^ 3 - 4009 * X ^ 4 + 1208 * X ^ 5 - 7 * X ^ 6 + X ^ 7) ∧
      ∀ n : ℕ, 4 < n → (a n : ℚ) = (3 / 32) * (5280 + 697 * 2 ^ n + 1840 * n + 208 * n ^ 2) := by
  sorry

end OMA.S_oeis_a253228
