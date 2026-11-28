import Mathlib

/-!
# A185089: a transform of the little Schroeder numbers

Source: https://oeis.org/A185089
Credit: @sntntHb

`a(n) = Sum_{k=0..floor(n/2)} binomial(n-k, k) * s(k)`, where `s = A001003` are the little
Schroeder numbers `1, 1, 3, 11, 45, 197, ...`. The entry records a conjecture of R. J. Mathar
(Nov 16 2011):
`(n+2)*a(n) - 3*(n+1)*a(n-1) + 3*(2-n)*a(n-2) + (11*n-20)*a(n-3) + (11-5*n)*a(n-4) + (4-n)*a(n-5) = 0`.

The little Schroeder numbers are written with Narayana numbers: `s(0) = 1` and, for `m ≥ 1`,
`s(m) = (Sum_{k=1..m} binomial(m, k) * binomial(m, k-1) * 2^(k-1)) / m`; the division is exact
(each term divided by `m` is a Narayana number times `2^(k-1)`). This gives
`1, 1, 3, 11, 45, 197, 903, ...` as in A001003, and `a` gives the listed data
`1, 1, 2, 3, 7, 14, 35, 81, 208, 517, ...` (checked numerically).

`main` states the recurrence, read in `ℤ`, for every `n ≥ 5` (the smallest `n` for which all
terms are defined); it was checked numerically for `5 ≤ n < 300`.
-/

namespace OMA.S_oeis_a185089

/-- The little Schroeder numbers `s m` (OEIS A001003), via Narayana numbers. -/
def s (m : ℕ) : ℕ :=
  if m = 0 then 1 else
    (∑ k ∈ Finset.Icc 1 m, Nat.choose m k * Nat.choose m (k - 1) * 2 ^ (k - 1)) / m

/-- `a n = Sum_{k=0..floor(n/2)} binomial(n-k, k) * s(k)` (OEIS A185089). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose (n - k) k * s k

/-- Mathar's conjectured recurrence for OEIS A185089. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℤ) + 2) * a n - 3 * ((n : ℤ) + 1) * a (n - 1) + 3 * (2 - (n : ℤ)) * a (n - 2)
      + (11 * (n : ℤ) - 20) * a (n - 3) + (11 - 5 * (n : ℤ)) * a (n - 4)
      + (4 - (n : ℤ)) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a185089
