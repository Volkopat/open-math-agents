import Mathlib

/-!
OEIS A191161: Hypersigma(n), definition 2: sum of the divisors of n plus the recursive sum
of the divisors of the proper divisors, i.e. a(n) = sigma(n) + Sum_{d|n, d<n} a(d)
(formula of Charles R Greathouse IV).

Formulas conjectured by Sequence Machine (Antti Karttunen, Nov 22 2024);
this file states three of them:
  (1) a(n) = Sum_{d|n} d * A067824(n/d);
  (2) a(n) = Sum_{d|n} A000203(d) * A074206(n/d);
  (3) a(n) = Sum_{d|n} A038040(d) * A323912(n/d).
Here
  A067824: B(1) = 1, B(n) = 1 + Sum_{d|n, d<n} B(d) for n > 1,
  A000203 = sigma,
  A074206 (Kalmar's problem): H(1) = 1, H(n) = Sum_{d|n, d<n} H(d) for n > 1,
  A038040(n) = n * tau(n), tau = number of divisors,
  A323912 is the Dirichlet inverse of 2*phi(n) - n:
    e(1) = 1, e(n) = -Sum_{d|n, d<n} (2*phi(n/d) - n/d) * e(d) for n > 1.
-/

namespace OMA.S_oeis_a191161

theorem main :
    ∀ a B H e : ℕ → ℤ,
      (∀ n : ℕ, 1 ≤ n →
        a n = (ArithmeticFunction.sigma 1 n : ℤ) + ∑ d ∈ n.properDivisors, a d) →
      (B 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → B n = 1 + ∑ d ∈ n.properDivisors, B d) →
      (H 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → H n = ∑ d ∈ n.properDivisors, H d) →
      (e 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
        e n = -∑ d ∈ n.properDivisors,
          (2 * (Nat.totient (n / d) : ℤ) - ((n / d : ℕ) : ℤ)) * e d) →
      ∀ n : ℕ, 1 ≤ n →
        a n = ∑ d ∈ n.divisors, (d : ℤ) * B (n / d) ∧
        a n = ∑ d ∈ n.divisors, (ArithmeticFunction.sigma 1 d : ℤ) * H (n / d) ∧
        a n = ∑ d ∈ n.divisors, ((d : ℤ) * (d.divisors.card : ℤ)) * e (n / d) := by
  sorry

end OMA.S_oeis_a191161
