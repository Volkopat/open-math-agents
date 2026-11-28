import Mathlib

/-!
# A115399: Expansion of c(x^2-x^3), c(x) the g.f. of A000108.

Source: https://oeis.org/A115399
Credit: @vivanpoddar

The sequence (offset 0) is 1, 0, -1, 1, 2, -4, -3, 15, -1, -51, 42, 154, ... The entry gives the formula
a(n) = Sum_{k=0..floor(n/2)} (-1)^(n-k)*C(k)*binomial(k, n-2k), with C(k) the Catalan numbers, which is
used here as the definition (it reproduces the data of the entry).

The conjecture (R. J. Mathar, Feb 20 2015) reads
(n+2)*a(n) + (-n-2)*a(n-1) + 4*(n-1)*a(n-2) + 2*(-4*n+7)*a(n-3) + 2*(2*n-5)*a(n-4) = 0.
It involves a(n-4), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a115399

/-- A115399 (offset 0): a(n) = Sum_{k=0..floor(n/2)} (-1)^(n-k)*Catalan(k)*binomial(k, n-2k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1), (-1) ^ (n - k) * (catalan k : ℤ) * (k.choose (n - 2 * k) : ℤ)

/-- Mathar's conjectured recurrence for A115399. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 2) * a n + (-(n : ℤ) - 2) * a (n - 1) + 4 * ((n : ℤ) - 1) * a (n - 2)
      + 2 * (-4 * (n : ℤ) + 7) * a (n - 3) + 2 * (2 * (n : ℤ) - 5) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a115399
