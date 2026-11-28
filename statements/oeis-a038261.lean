import Mathlib

/-!
# A038261: First line of 5-wave sequence A038201, also bisection of A006358.

Source: https://oeis.org/A038261 (conjecture by Wouter Meeussen, Mar 19 2005)

Conjecture: GF = -(x-1)*(x^3-6*x^2+9*x-1) / ( -1+15*x-35*x^2+28*x^3-9*x^4+x^5 ).

Conventions. The 5-wave sequence A038201 (offset 0) is defined by its recurrence in that
entry: `w(0) = ... = w(4) = 1` (the first five listed terms) and, for `n >= 5`,
`w(n) = w(n-1) + w(n-2)` if `n = 4m+1`, `w(n) = w(n-1) + w(n-4)` if `n = 4m+2`,
`w(n) = w(n-1) + w(n-6)` if `n = 4m+3`, `w(n) = w(n-1) + w(n-8)` if `n = 4m`.
Its first line, i.e. the sequence A038261 (offset 0) with listed terms
1, 5, 55, 671, 8272, 102091, ..., is `a(n) = w(8n)` (this reproduces the listed terms; it is
also every other term of the subsequence `w(4m)`, which is A006358 shifted by one).

Since the denominator has constant term `-1`, which is a unit, the generating function
identity is equivalent to the stated product identity of formal power series over `ℤ`.
-/

namespace OMA.S_oeis_a038261

open PowerSeries

/-- The 5-wave sequence A038201. -/
def w (n : ℕ) : ℕ :=
  if h : n ≤ 4 then 1
  else if n % 4 = 1 then w (n - 1) + w (n - 2)
  else if n % 4 = 2 then w (n - 1) + w (n - 4)
  else if n % 4 = 3 then w (n - 1) + w (n - 6)
  else w (n - 1) + w (n - 8)
decreasing_by all_goals omega

/-- A038261: `a(n) = w(8n)`. -/
def a (n : ℕ) : ℕ := w (8 * n)

theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
        (-1 + 15 * X - 35 * X ^ 2 + 28 * X ^ 3 - 9 * X ^ 4 + X ^ 5) =
      -(X - 1) * (X ^ 3 - 6 * X ^ 2 + 9 * X - 1) := by
  sorry

end OMA.S_oeis_a038261
