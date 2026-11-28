import Mathlib

/-!
# A065942: central column of triangle A065941

Source: https://oeis.org/A065942 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

A065941 is the triangle `T(n,k) = binomial(n - floor((k+1)/2), floor(k/2))`, `0 ≤ k ≤ n`
(rows `1; 1, 1; 1, 1, 1; 1, 1, 2, 1; ...`). Its central column is `a(n) = T(2n, n)`.
Offset `0`, data `1, 1, 3, 4, 15, 21, 84, 120, 495, 715, ...`.

Conjecture (R. J. Mathar):
`8*n*(n-1)*a(n) - 36*(n-1)*(n-3)*a(n-1) + 6*(-9*n^2+18*n-14)*a(n-2)
 + 27*(3*n-7)*(3*n-8)*a(n-3) = 0`, for `n ≥ 3` (the indices where `a(n-3)` is defined).
This is a known result: `a(n) = binomial(n + floor(n/2), n)` (P. Barry), which is hypergeometric
in `n` along each parity class.
-/

namespace OMA.S_oeis_a065942

/-- The triangle A065941: `T(n,k) = binomial(n - floor((k+1)/2), floor(k/2))`. -/
def T (n k : ℕ) : ℕ := (n - (k + 1) / 2).choose (k / 2)

/-- A065942: the central column `a(n) = T(2n, n)` of A065941. -/
def a (n : ℕ) : ℕ := T (2 * n) n

/-- Conjecture (R. J. Mathar): the order-3 P-recurrence of A065942, for `n ≥ 3`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      8 * (n : ℤ) * (n - 1) * a n - 36 * ((n : ℤ) - 1) * (n - 3) * a (n - 1)
        + 6 * (-9 * (n : ℤ) ^ 2 + 18 * n - 14) * a (n - 2)
        + 27 * (3 * (n : ℤ) - 7) * (3 * n - 8) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a065942
