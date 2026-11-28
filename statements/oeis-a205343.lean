import Mathlib

/-!
# A205343: length 6 arrays from 0 to 0 with adjacent elements unequal, differing by at most n

A205343(n) is the number of length 6 nonnegative integer arrays `x 0, ..., x 5` with
`x 0 = 0`, `x 5 = 0` and, for every pair of adjacent elements, `x i ≠ x (i + 1)` and
`|x i - x (i + 1)| ≤ n`. (Such arrays are bounded by `2 * n`, so the set is finite.)
A brute-force count of this reading gives 0, 24, 138, 454, 1130 for n = 1..5, matching
the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function.

The problem: the conjectures of Colin Barker (Jun 11 2018):
  G.f.: 2*x^2*(12 + 9*x + 2*x^2) / (1 - x)^5,
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 5.
The g.f. is stated after multiplying both sides by (1 - x)^5. (R. H. Hardin's empirical
polynomial follows from the g.f.)

Source: https://oeis.org/A205343
Credit: @VashaTS
-/

namespace OMA.S_oeis_a205343

open PowerSeries

/-- The length 6 nonnegative integer arrays starting and ending with 0 whose adjacent
elements are unequal but differ by at most `n`. -/
def arrays (n : ℕ) : Set (Fin 6 → ℕ) :=
  {x | x 0 = 0 ∧ x 5 = 0 ∧
    ∀ i : Fin 6, ∀ j : Fin 6, j.val = i.val + 1 → x i ≠ x j ∧ |(x i : ℤ) - x j| ≤ n}

/-- A205343(n). -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).ncard

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      2 * X ^ 2 * (12 + 9 * X + 2 * X ^ 2) ∧
    ∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a205343
