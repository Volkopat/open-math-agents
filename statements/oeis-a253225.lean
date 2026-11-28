import Mathlib

/-!
# OEIS A253225: Barker's g.f. and closed form for (n+1) X 3 binary arrays with 2 X 2 diagonal minus antidiagonal minima nondecreasing horizontally and maxima vertically

Source: https://oeis.org/A253225 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A253225 (R. H. Hardin, Dec 29 2014), offset 1: Number of (n+1) X (2+1) 0..1 arrays with every
2 X 2 subblock diagonal minimum minus antidiagonal minimum nondecreasing horizontally and diagonal
maximum minus antidiagonal maximum nondecreasing vertically. Column 2 of A253231. Data: 47, 132,
306, 742, 1775, ... Formula section: Empirical recurrence. Conjectures from Colin Barker, Dec 10
2018: (Start) G.f.: x*(47 - 103*x + 22*x^2 + 80*x^3 - 15*x^4 - 5*x^5 - 7*x^6) / ((1 - x)*(1 -
2*x)^2). a(n) = 19 + 377*2^(n-6) + 627*2^(n-6)*n for n>4. (End)

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 3 -> Fin 2, x i j being the element in row i and
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
* Controls proved in the proof file: a(1..26) = 47, 132, 306, 742, 1775, 4158, 9551, 21591, 48179,
  106371, 232787, 505683, 1091603, 2343699, 5008403, 10658835, 22601747, 47771667, 100679699,
  211632147, 443809811, 928710675, 1939603475, 4043571219, 8415870995, 17489199123, the entry's
  data.
-/

namespace OMA.S_oeis_a253225

open PowerSeries

/-- A253225(n): the number of (n+1) X 3 arrays x with entries 0..1 (x i j in row i and column j) in
which, for the 2 X 2 subblocks B(i,j) with rows i, i + 1 and columns j, j + 1, the diagonal minimum
minus the antidiagonal minimum, min(x(i,j), x(i+1,j+1)) - min(x(i,j+1), x(i+1,j)), is nondecreasing
horizontally (from B(i,j) to B(i,j+1)) and the diagonal maximum minus the antidiagonal maximum is
nondecreasing vertically (from B(i,j) to B(i+1,j)). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 3 → Fin 2)).filter (fun x =>
    (∀ i i' : Fin (n + 1), i'.val = i.val + 1 →
      (∀ j j' j'' : Fin 3, j'.val = j.val + 1 → j''.val = j'.val + 1 → (min ((x i j).val : ℤ) ((x i' j').val : ℤ) - min ((x i j').val : ℤ) ((x i' j).val : ℤ) ≤
              min ((x i j').val : ℤ) ((x i' j'').val : ℤ) - min ((x i j'').val : ℤ) ((x i' j').val : ℤ)))) ∧
    ∀ i i' i'' : Fin (n + 1), i'.val = i.val + 1 → i''.val = i'.val + 1 →
      (∀ j j' : Fin 3, j'.val = j.val + 1 → (max ((x i j).val : ℤ) ((x i' j').val : ℤ) - max ((x i j').val : ℤ) ((x i' j).val : ℤ) ≤
              max ((x i' j).val : ℤ) ((x i'' j').val : ℤ) - max ((x i' j').val : ℤ) ((x i'' j).val : ℤ))))).card

/-- Barker's conjectures: the g.f. and the closed form for n > 4. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) ^ 2) =
        X * (47 - 103 * X + 22 * X ^ 2 + 80 * X ^ 3 - 15 * X ^ 4 - 5 * X ^ 5 - 7 * X ^ 6) ∧
      ∀ n : ℕ, 4 < n → (a n : ℚ) = 19 + 377 * 2 ^ ((n : ℤ) - 6) + 627 * 2 ^ ((n : ℤ) - 6) * n := by
  sorry

end OMA.S_oeis_a253225
