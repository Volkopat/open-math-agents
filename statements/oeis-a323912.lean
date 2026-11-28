import Mathlib

/-!
OEIS A323912: Dirichlet inverse of A083254(n), where A083254(n) = 2*phi(n) - n.
a(1) = 1, and for n > 1, a(n) = -Sum_{d|n, d<n} A083254(n/d) * a(d).

Convolution formulas conjectured by Sequence Machine (Antti Karttunen, Nov 22 2024);
this file states two of them:
  (1) a(n) = Sum_{d|n} A023900(d) * A074206(n/d)
      (the variant Sum_{d|n} A002033(d-1) * A023900(n/d) is the same convolution,
      since A002033(d-1) = A074206(d) for d >= 1);
  (2) a(n) = Sum_{d|n} A055615(d) * A067824(n/d).
Here
  A023900 is the Dirichlet inverse of Euler's totient phi,
  A074206 (Kalmar's problem): H(1) = 1, H(n) = Sum_{d|n, d<n} H(d) for n > 1,
  A055615(n) = n * mu(n),
  A067824: B(1) = 1, B(n) = 1 + Sum_{d|n, d<n} B(d) for n > 1.
-/

namespace OMA.S_oeis_a323912

theorem main :
    ∀ a c H B : ℕ → ℤ,
      (a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
        a n = -∑ d ∈ n.properDivisors,
          (2 * (Nat.totient (n / d) : ℤ) - ((n / d : ℕ) : ℤ)) * a d) →
      (∀ n : ℕ, 1 ≤ n →
        ∑ d ∈ n.divisors, c d * (Nat.totient (n / d) : ℤ) = if n = 1 then 1 else 0) →
      (H 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → H n = ∑ d ∈ n.properDivisors, H d) →
      (B 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → B n = 1 + ∑ d ∈ n.properDivisors, B d) →
      ∀ n : ℕ, 1 ≤ n →
        a n = ∑ d ∈ n.divisors, c d * H (n / d) ∧
        a n = ∑ d ∈ n.divisors, ((d : ℤ) * ArithmeticFunction.moebius d) * B (n / d) := by
  sorry

end OMA.S_oeis_a323912
