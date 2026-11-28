import Mathlib

/-!
# OEIS A253229: Barker's g.f. and closed form for (n+1) X 7 binary arrays with 2 X 2 diagonal minus antidiagonal minima nondecreasing horizontally and maxima vertically

Source: https://oeis.org/A253229 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A253229 (R. H. Hardin, Dec 29 2014), offset 1: Number of (n+1) X (6+1) 0..1 arrays with every
2 X 2 subblock diagonal minimum minus antidiagonal minimum nondecreasing horizontally and diagonal
maximum minus antidiagonal maximum nondecreasing vertically. Column 6 of A253231. Data: 2470, 4158, 3241, 4490, 6414, ...
Formula section: Empirical recurrence. Conjectures from Colin Barker, Dec 10 2018: (Start)
G.f.: x*(2470 - 8192*x + 4681*x^2 + 8417*x^3 - 11033*x^4 + 3599*x^5 - 9*x^6 + x^7) / ((1 - x)^3*(1 - 2*x)).
a(n) = 1128 + 2451*2^(n-5) + 402*n + 33*n^2 for n>4.
(End)

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 7 -> Fin 2, x i j being the element in row i and
  column j. For the 2 X 2 subblock B(i,j) with rows i, i' = i + 1 and columns j, j' = j + 1 the
  diagonal is x(i,j), x(i',j') and the antidiagonal x(i,j'), x(i',j). Nondecreasing horizontally
  compares each block with its right neighbor B(i,j') (j'' = j' + 1 below); nondecreasing
  vertically compares it with the block below, B(i',j) (i'' = i' + 1). Differences are taken in Z.
  This is the reading of the sister statements of A253228 and its neighbors; it reproduces every
  listed term of the entry (checked by a transfer on pairs of rows, and by brute force over all
  arrays for the first terms).
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal to
  the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed form: 2^(n-5) is a natural-number power, an integer for every n > 4, the range given in the source.
* `main` is the conjunction of Barker's two conjectures.
* Data of the entry, from n = 1: 2470, 4158, 3241, 4490, 6414, 9630, 15363, 26064, 46635, 86880, 166407, 324432, 639387, 1268136, 2524407, 5035656, 10056795, 20097648, 40177863, 80336736, 160652859, 321283416, 642542775, 1285059672, 2570091579, 5140153440.
-/

namespace OMA.S_oeis_a253229

open PowerSeries

/-- A253229(n): the number of (n+1) X 7 arrays x with entries 0..1 (x i j in row i and column j) in
which, for the 2 X 2 subblocks B(i,j) with rows i, i + 1 and columns j, j + 1, the diagonal minimum
minus the antidiagonal minimum, min(x(i,j), x(i+1,j+1)) - min(x(i,j+1), x(i+1,j)), is nondecreasing
horizontally (from B(i,j) to B(i,j+1)) and the diagonal maximum minus the antidiagonal maximum,
max(x(i,j), x(i+1,j+1)) - max(x(i,j+1), x(i+1,j)), is nondecreasing vertically (from B(i,j) to
B(i+1,j)). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 7 → Fin 2)).filter (fun x =>
    (∀ i i' : Fin (n + 1), i'.val = i.val + 1 →
      ∀ j j' j'' : Fin 7, j'.val = j.val + 1 → j''.val = j'.val + 1 →
        min ((x i j).val : ℤ) ((x i' j').val : ℤ) - min ((x i j').val : ℤ) ((x i' j).val : ℤ) ≤
          min ((x i j').val : ℤ) ((x i' j'').val : ℤ) - min ((x i j'').val : ℤ) ((x i' j').val : ℤ)) ∧
    ∀ i i' i'' : Fin (n + 1), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      ∀ j j' : Fin 7, j'.val = j.val + 1 →
        max ((x i j).val : ℤ) ((x i' j').val : ℤ) - max ((x i j').val : ℤ) ((x i' j).val : ℤ) ≤
          max ((x i' j).val : ℤ) ((x i'' j').val : ℤ) - max ((x i' j').val : ℤ) ((x i'' j).val : ℤ))).card

/-- Barker's conjectures: the g.f. and the closed form for n > 4. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 - 2 * X)) =
        X * (2470 - 8192 * X + 4681 * X ^ 2 + 8417 * X ^ 3 - 11033 * X ^ 4 + 3599 * X ^ 5 - 9 * X ^ 6 + X ^ 7) ∧
      ∀ n : ℕ, 4 < n → (a n : ℚ) = 1128 + 2451 * 2 ^ (n - 5) + 402 * n + 33 * n ^ 2 := by
  sorry

end OMA.S_oeis_a253229
