import Mathlib

/-!
# A081205: staircase on Pascal's triangle

Source: https://oeis.org/A081205 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

Arrange Pascal's triangle as a square array; A081204 is a diagonal staircase on it, and this
sequence takes the steps `(1,3), (10,20), (70,126), ...`.
We use the formula listed in the entry, `a(n) = binomial(ceiling((n+1)/2) + (n+1), n)`;
in `ℕ`, `ceiling((n+1)/2) = (n+2)/2` (floor division).
Offset `0`, data `1, 3, 10, 20, 70, 126, 462, 792, 3003, 5005, ...`.

Conjecture (R. J. Mathar, Nov 19 2014):
`4*n*(n-1)*(n+4)*(6*n^2-9*n-1)*a(n) + 6*(n-1)*(27*n^2+29*n+4)*a(n-1)
 - 3*n*(3*n-1)*(3*n+1)*(6*n^2+3*n-4)*a(n-2) = 0`, for `n ≥ 2` (the indices where `a(n-2)` is
defined). This is a known result: `a(2m) = binomial(3m+2, 2m)` and
`a(2m+1) = binomial(3m+3, 2m+1)`, so `a(n)` is hypergeometric along each parity class.
-/

namespace OMA.S_oeis_a081205

/-- A081205: `a(n) = binomial(ceiling((n+1)/2) + (n+1), n)`. -/
def a (n : ℕ) : ℕ := ((n + 2) / 2 + (n + 1)).choose n

/-- Conjecture (R. J. Mathar): the order-2 P-recurrence of A081205, for `n ≥ 2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      4 * (n : ℤ) * (n - 1) * (n + 4) * (6 * n ^ 2 - 9 * n - 1) * a n
        + 6 * ((n : ℤ) - 1) * (27 * n ^ 2 + 29 * n + 4) * a (n - 1)
        - 3 * (n : ℤ) * (3 * n - 1) * (3 * n + 1) * (6 * n ^ 2 + 3 * n - 4) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a081205
