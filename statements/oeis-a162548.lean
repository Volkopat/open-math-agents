import Mathlib

/-!
# A162548: a conjectured recurrence for a Chebyshev transform of the little Schroeder numbers

Source: https://oeis.org/A162548
Credit: @sntntHb

`a(n)` (offset 0) is the Chebyshev transform
`a(n) = Sum_{k=0..floor(n/2)} (-1)^k binomial(n-k, k) s(n-2k)` of the little Schroeder numbers
`s = A001003` (`1, 1, 3, 11, 45, 197, ...`), with generating function `s(x/(1+x^2)) / (1+x^2)`. The
data starts `1, 1, 2, 9, 37, 156, 695, 3203, 15118, ...`.

The little Schroeder numbers are `s(0) = 1` and, for `m ≥ 1`, the Narayana sum
`s(m) = Sum_{k=1..m} N(m, k) 2^(k-1)` with `N(m, k) = binomial(m, k) binomial(m, k-1) / m`;
here `m s(m) = Sum_{k=1..m} binomial(m, k) binomial(m, k-1) 2^(k-1)` is used, the division being
exact.

The entry records the conjecture (R. J. Mathar, Nov 15 2012)
`(n+1) a(n) + 3(-2n+1) a(n-1) + (4n-5) a(n-2) + 12(-n+2) a(n-3) + (4n-11) a(n-4)
 + 3(-2n+7) a(n-5) + (n-5) a(n-6) = 0`,
stated for `n ≥ 6` so that every index is a valid term (if earlier terms are read as `0` it
fails at `n = 4` and holds at `n = 5`).
-/

namespace OMA.S_oeis_a162548

/-- The little Schroeder numbers A001003. -/
def s (m : ℕ) : ℕ :=
  if m = 0 then 1 else
    (∑ k ∈ Finset.Icc 1 m, m.choose k * m.choose (k - 1) * 2 ^ (k - 1)) / m

/-- OEIS A162548. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1), ((-1) ^ k * ((n - k).choose k : ℤ) * s (n - 2 * k))

/-- Mathar's conjectured recurrence for A162548. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℤ) + 1) * a n + 3 * (-2 * (n : ℤ) + 1) * a (n - 1) + (4 * (n : ℤ) - 5) * a (n - 2) +
      12 * (-(n : ℤ) + 2) * a (n - 3) + (4 * (n : ℤ) - 11) * a (n - 4) +
      3 * (-2 * (n : ℤ) + 7) * a (n - 5) + ((n : ℤ) - 5) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a162548
