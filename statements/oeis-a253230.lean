import Mathlib

/-!
# OEIS A253230: Barker's g.f. and closed form for (n+1) X 8 binary arrays with 2 X 2 diagonal minus antidiagonal minima nondecreasing horizontally and maxima vertically

Source: https://oeis.org/A253230 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A253230 (R. H. Hardin, Dec 29 2014), offset 1: Number of (n+1) X (7+1) 0..1 arrays with every
2 X 2 subblock diagonal minimum minus antidiagonal minimum nondecreasing horizontally and diagonal
maximum minus antidiagonal maximum nondecreasing vertically. Column 7 of A253231. Data: 6740, 9551, 6231, 8216, 11022, ...
Formula section: Empirical recurrence. Conjectures from Colin Barker, Dec 11 2018: (Start)
G.f.: x*(6740 - 24149*x + 19136*x^2 + 15840*x^3 - 27356*x^4 + 9682*x^5 - 11*x^6 + x^7) / ((1 - x)^3*(1 - 2*x)).
a(n) = (3/32)*(25728 + 945*2^n + 9200*n + 624*n^2) for n>4.
(End)

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 8 -> Fin 2, x i j being the element in row i and
  column j. For the 2 X 2 subblock B(i,j) with rows i, i' = i + 1 and columns j, j' = j + 1 the
  diagonal is x(i,j), x(i',j') and the antidiagonal x(i,j'), x(i',j). Nondecreasing horizontally
  compares each block with its right neighbor B(i,j') (j'' = j' + 1 below); nondecreasing
  vertically compares it with the block below, B(i',j) (i'' = i' + 1). Differences are taken in Z.
  This is the reading of the sister statements of A253228 and its neighbors; it reproduces every
  listed term of the entry (checked by a transfer on pairs of rows, and by brute force over all
  arrays for the first terms).
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) times the denominator equal to
  the numerator in Q[[x]], which is equivalent to the quotient form because the denominator has
  constant term 1. The closed form: it is stated in Q for n > 4, the range given in the source.
* `main` is the conjunction of Barker's two conjectures.
* Data of the entry, from n = 1: 6740, 9551, 6231, 8216, 11022, 15363, 22656, 35736, 60273, 107607, 200418, 384066, 749271, 1477473, 2931552, 5837268, 11646141, 23261211, 46488558, 92940342, 185840883, 371638821, 743231436, 1486413288, 2972773497, 5945490303.
-/

namespace OMA.S_oeis_a253230

open PowerSeries

/-- A253230(n): the number of (n+1) X 8 arrays x with entries 0..1 (x i j in row i and column j) in
which, for the 2 X 2 subblocks B(i,j) with rows i, i + 1 and columns j, j + 1, the diagonal minimum
minus the antidiagonal minimum, min(x(i,j), x(i+1,j+1)) - min(x(i,j+1), x(i+1,j)), is nondecreasing
horizontally (from B(i,j) to B(i,j+1)) and the diagonal maximum minus the antidiagonal maximum,
max(x(i,j), x(i+1,j+1)) - max(x(i,j+1), x(i+1,j)), is nondecreasing vertically (from B(i,j) to
B(i+1,j)). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 8 → Fin 2)).filter (fun x =>
    (∀ i i' : Fin (n + 1), i'.val = i.val + 1 →
      ∀ j j' j'' : Fin 8, j'.val = j.val + 1 → j''.val = j'.val + 1 →
        min ((x i j).val : ℤ) ((x i' j').val : ℤ) - min ((x i j').val : ℤ) ((x i' j).val : ℤ) ≤
          min ((x i j').val : ℤ) ((x i' j'').val : ℤ) - min ((x i j'').val : ℤ) ((x i' j').val : ℤ)) ∧
    ∀ i i' i'' : Fin (n + 1), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      ∀ j j' : Fin 8, j'.val = j.val + 1 →
        max ((x i j).val : ℤ) ((x i' j').val : ℤ) - max ((x i j').val : ℤ) ((x i' j).val : ℤ) ≤
          max ((x i' j).val : ℤ) ((x i'' j').val : ℤ) - max ((x i' j').val : ℤ) ((x i'' j).val : ℤ))).card

/-- Barker's conjectures: the g.f. and the closed form for n > 4. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 - 2 * X)) =
        X * (6740 - 24149 * X + 19136 * X ^ 2 + 15840 * X ^ 3 - 27356 * X ^ 4 + 9682 * X ^ 5 - 11 * X ^ 6 + X ^ 7) ∧
      ∀ n : ℕ, 4 < n → (a n : ℚ) = (3 / 32) * (25728 + 945 * 2 ^ n + 9200 * n + 624 * n ^ 2) := by
  sorry

end OMA.S_oeis_a253230
