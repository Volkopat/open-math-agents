import Mathlib

/-!
OEIS A191150: Hypersigma(n), definition 1: sum of the divisors of n plus the recursive sum of
the divisors of the restricted divisors.
We use the characterization a(1) = 1 and, for n > 1, a(n) = n - 1 + Sum_{d|n, d<n} (a(d) + d)
(formula of Chai Wah Wu, Mar 24 2026).

Conjecture (Sequence Machine, Antti Karttunen, Nov 22 2024):
for n > 1, a(n) = A191161(n) - A074206(n), where
  A191161 (hypersigma, definition 2): g(n) = sigma(n) + Sum_{d|n, d<n} g(d),
  A074206 (Kalmar's problem): H(1) = 1, H(n) = Sum_{d|n, d<n} H(d) for n > 1.
-/

namespace OMA.S_oeis_a191150

theorem main :
    ∀ a g H : ℕ → ℤ,
      (a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
        a n = (n : ℤ) - 1 + ∑ d ∈ n.properDivisors, (a d + d)) →
      (∀ n : ℕ, 1 ≤ n →
        g n = (ArithmeticFunction.sigma 1 n : ℤ) + ∑ d ∈ n.properDivisors, g d) →
      (H 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → H n = ∑ d ∈ n.properDivisors, H d) →
      ∀ n : ℕ, 2 ≤ n → a n = g n - H n := by
  sorry

end OMA.S_oeis_a191150
