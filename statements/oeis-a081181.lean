import Mathlib

/-!
# A081181: staircase on Pascal's triangle

Source: https://oeis.org/A081181 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

Arrange Pascal's triangle as a square array; this sequence is a diagonal staircase on it
(a companion staircase is A065942).
We use the formula listed in the entry, `a(n) = binomial(floor((n + 1)/2) + (n + 1), n)`.
Offset `0`, data `1, 3, 6, 20, 35, 126, 210, 792, 1287, 5005, ...`.

Conjecture (R. J. Mathar, Oct 29 2014):
`8*n*(n+3)*(1845*n-2882)*a(n) + 4*(-5097*n^3+11143*n^2 + 42110*n-27416)*a(n-1)
 + 6*(-16605*n^3-7272*n^2-16701*n+9490)*a(n-2) + 3*(3*n-5)*(5097*n-949)*(3*n-4)*a(n-3) = 0`,
for `n ≥ 3` (the indices where `a(n-3)` is defined). This is a known result:
`a(2m) = binomial(3m+1, 2m)` and `a(2m+1) = binomial(3m+3, 2m+1)`, so `a(n)` is hypergeometric
along each parity class.
-/

namespace OMA.S_oeis_a081181

/-- A081181: `a(n) = binomial(floor((n + 1)/2) + (n + 1), n)`. -/
def a (n : ℕ) : ℕ := ((n + 1) / 2 + (n + 1)).choose n

/-- Conjecture (R. J. Mathar): the order-3 P-recurrence of A081181, for `n ≥ 3`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      8 * (n : ℤ) * (n + 3) * (1845 * n - 2882) * a n
        + 4 * (-5097 * (n : ℤ) ^ 3 + 11143 * n ^ 2 + 42110 * n - 27416) * a (n - 1)
        + 6 * (-16605 * (n : ℤ) ^ 3 - 7272 * n ^ 2 - 16701 * n + 9490) * a (n - 2)
        + 3 * (3 * (n : ℤ) - 5) * (5097 * n - 949) * (3 * n - 4) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a081181
