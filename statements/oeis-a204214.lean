import Mathlib

/-!
# A204214: length 6 arrays from 0 to 0 with adjacent differences at most n

A204214(n) is the number of length 6 nonnegative integer arrays `x 0, ..., x 5` with
`x 0 = 0`, `x 5 = 0` and `|x i - x (i + 1)| ≤ n` for every pair of adjacent elements.
(Such arrays are bounded by `2 * n`, so the set is finite.) A brute-force count of this
reading gives 21, 120, 404, 1025, 2181, 4116 for n = 1..6, matching the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Jun 06 2018):
  G.f.: x*(21 + 15*x + 14*x^2 - 5*x^3 + x^4) / (1 - x)^5,
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 5.
The g.f. is stated after multiplying both sides by (1 - x)^5. (R. H. Hardin's empirical
polynomial follows from the g.f.)

Source: https://oeis.org/A204214
Credit: @VashaTS
-/

namespace OMA.S_oeis_a204214

open PowerSeries

/-- The length 6 nonnegative integer arrays starting and ending with 0 whose adjacent
elements differ by at most `n`. -/
def arrays (n : ℕ) : Set (Fin 6 → ℕ) :=
  {x | x 0 = 0 ∧ x 5 = 0 ∧
    ∀ i : Fin 6, ∀ j : Fin 6, j.val = i.val + 1 → |(x i : ℤ) - x j| ≤ n}

/-- A204214(n). -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).ncard

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (21 + 15 * X + 14 * X ^ 2 - 5 * X ^ 3 + X ^ 4) ∧
    ∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a204214
