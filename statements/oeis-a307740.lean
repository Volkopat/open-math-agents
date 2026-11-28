import Mathlib

/-!
# A307740: Numbers k such that k divides lcm(tau(k), sigma(k)).

Source: https://oeis.org/A307740
Credit: @agchua

Comment of A307740 (unsigned; the entry is by Jaroslav Krizek, Apr 26 2019):
  Conjecture: multiply-perfect numbers (A007691) are terms.
Offset 1, first term 1. Here tau(k) is the number of divisors of k (A000005) and sigma(k) is the
sum of the divisors of k (A000203). A multiply-perfect number (A007691: 1, 6, 28, 120, 496, ...)
is a positive k that divides sigma(k). The conjecture says that every such k is a term, i.e. that
k divides lcm(tau(k), sigma(k)). It is stated for every k >= 1.
-/

namespace OMA.S_oeis_a307740

/-- tau(k) = A000005(k), the number of divisors of k. -/
def tau (k : ℕ) : ℕ := (Nat.divisors k).card

/-- sigma(k) = A000203(k), the sum of the divisors of k. -/
def sigma (k : ℕ) : ℕ := ∑ d ∈ Nat.divisors k, d

/-- The conjecture: every multiply-perfect number k (k divides sigma(k)) is a term of A307740,
that is, k divides lcm(tau(k), sigma(k)). -/
theorem main : ∀ k : ℕ, 1 ≤ k → k ∣ sigma k → k ∣ Nat.lcm (tau k) (sigma k) := by
  sorry

end OMA.S_oeis_a307740
