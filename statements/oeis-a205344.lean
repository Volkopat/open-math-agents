import Mathlib

/-!
# A205344: length 7 arrays from 0 to 0 with adjacent elements unequal, differing by at most n

A205344(n) is the number of length 7 nonnegative integer arrays `x 0, ..., x 6` with
`x 0 = 0`, `x 6 = 0` and, for every pair of adjacent elements, `x i ≠ x (i + 1)` and
`|x i - x (i + 1)| ≤ n`. (Such arrays are bounded by `3 * n`, so the set is finite.)
A brute-force count of this reading gives 5, 93, 689, 2912 for n = 1..4, matching the
listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Jun 11 2018):
  G.f.: x*(5 + 63*x + 206*x^2 + 73*x^3 + 5*x^4) / (1 - x)^6,
  a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n > 6.
The g.f. is stated after multiplying both sides by (1 - x)^6. (R. H. Hardin's empirical
polynomial follows from the g.f.)

Source: https://oeis.org/A205344
Credit: @VashaTS
-/

namespace OMA.S_oeis_a205344

open PowerSeries

/-- The length 7 nonnegative integer arrays starting and ending with 0 whose adjacent
elements are unequal but differ by at most `n`. -/
def arrays (n : ℕ) : Set (Fin 7 → ℕ) :=
  {x | x 0 = 0 ∧ x 6 = 0 ∧
    ∀ i : Fin 7, ∀ j : Fin 7, j.val = i.val + 1 → x i ≠ x j ∧ |(x i : ℤ) - x j| ≤ n}

/-- A205344(n). -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).ncard

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
      X * (5 + 63 * X + 206 * X ^ 2 + 73 * X ^ 3 + 5 * X ^ 4) ∧
    ∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4)
        + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a205344
