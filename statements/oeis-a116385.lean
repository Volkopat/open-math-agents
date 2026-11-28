import Mathlib

/-!
# A116385: Expansion of e.g.f. Bessel_I(2,2x) + 2*Bessel_I(3,2x) + Bessel_I(4,2x).

Source: https://oeis.org/A116385
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 1, 2, 5, 10, 21, 42, 84, 168, 330, 660, 1287, 2574, 5005, 10010, ...

Definition. The modified Bessel function has the series I_k(2x) = Sum_{m>=0} x^(2m+k) / (m! (m+k)!), so the
coefficient of x^n/n! in I_k(2x) is n!/(m! (m+k)!) = binomial(n, m) when n = 2m + k, and 0 when n < k or
n - k is odd. This is `besselCoeff k n` below, and a(n) is the coefficient of x^n/n! in the e.g.f. of the
name, a(n) = besselCoeff 2 n + 2*besselCoeff 3 n + besselCoeff 4 n (it reproduces the data of the entry).

The conjecture (R. J. Mathar, Jun 13 2014) reads
  Conjecture: (n+4)*a(n) -2*a(n-1) +(-7*n-8)*a(n-2) +6*a(n-3) +12*(n-2)*a(n-4)=0.
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a116385

/-- The coefficient of x^n/n! in Bessel_I(k, 2x): binomial(n, (n-k)/2) if n ≥ k and n - k is even, else 0. -/
def besselCoeff (k n : ℕ) : ℤ :=
  if k ≤ n ∧ (n - k) % 2 = 0 then (n.choose ((n - k) / 2) : ℤ) else 0

/-- A116385: the coefficient of x^n/n! in Bessel_I(2,2x) + 2*Bessel_I(3,2x) + Bessel_I(4,2x). -/
def a (n : ℕ) : ℤ := besselCoeff 2 n + 2 * besselCoeff 3 n + besselCoeff 4 n

/-- Mathar's conjectured recurrence for A116385. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 4) * a n - 2 * a (n - 1) + (-7 * (n : ℤ) - 8) * a (n - 2) + 6 * a (n - 3)
      + 12 * ((n : ℤ) - 2) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a116385
