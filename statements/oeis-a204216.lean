import Mathlib

/-!
# A204216: length 8 arrays from 0 to 0 with adjacent differences at most n

A204216(n) is the number of length 8 nonnegative integer arrays `x 0, ..., x 7` with
`x 0 = 0`, `x 7 = 0` and `|x i - x (i + 1)| ≤ n` for every pair of adjacent elements.
(Such arrays are bounded by `4 * n`, so the set is finite.) A brute-force count of this
reading gives 127, 1925, 12492 for n = 1..3, matching the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Jun 06 2018):
  G.f.: x*(127 + 1036*x + 1684*x^2 + 481*x^3 + 42*x^4 - 7*x^5 + x^6) / (1 - x)^7,
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7)
  for n > 7.
The g.f. is stated after multiplying both sides by (1 - x)^7. (R. H. Hardin's empirical
polynomial follows from the g.f.)

Source: https://oeis.org/A204216
Credit: @VashaTS
-/

namespace OMA.S_oeis_a204216

open PowerSeries

/-- The length 8 nonnegative integer arrays starting and ending with 0 whose adjacent
elements differ by at most `n`. -/
def arrays (n : ℕ) : Set (Fin 8 → ℕ) :=
  {x | x 0 = 0 ∧ x 7 = 0 ∧
    ∀ i : Fin 8, ∀ j : Fin 8, j.val = i.val + 1 → |(x i : ℤ) - x j| ≤ n}

/-- A204216(n). -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).ncard

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (127 + 1036 * X + 1684 * X ^ 2 + 481 * X ^ 3 + 42 * X ^ 4 - 7 * X ^ 5 + X ^ 6) ∧
    ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4)
        + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a204216
