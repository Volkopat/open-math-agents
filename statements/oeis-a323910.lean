import Mathlib

/-!
OEIS A323910: Dirichlet inverse of the deficiency of n, A033879(n) = 2*n - sigma(n).
a(1) = 1, and for n > 1, a(n) = -Sum_{d|n, d<n} A033879(n/d) * a(d).

Convolution formulas conjectured by Sequence Machine (Antti Karttunen, Nov 14 2024);
this file states three of them:
  (1) a(n) = Sum_{d|n} A046692(d) * A067824(n/d);
  (2) a(n) = Sum_{d|n} A055615(d) * A074206(n/d)
      (the variant Sum_{d|n} A002033(d-1) * A055615(n/d) is the same convolution,
      since A002033(d-1) = A074206(d) for d >= 1);
  (3) a(n) = Sum_{d|n} A008683(d) * A323912(n/d).
Here
  A046692 is the Dirichlet inverse of sigma = A000203,
  A067824: B(1) = 1, B(n) = 1 + Sum_{d|n, d<n} B(d) for n > 1,
  A055615(n) = n * mu(n),
  A074206 (Kalmar's problem): H(1) = 1, H(n) = Sum_{d|n, d<n} H(d) for n > 1,
  A008683 = mu,
  A323912 is the Dirichlet inverse of 2*phi(n) - n:
    e(1) = 1, e(n) = -Sum_{d|n, d<n} (2*phi(n/d) - n/d) * e(d) for n > 1.
-/

namespace OMA.S_oeis_a323910

theorem main :
    ∀ a s B H e : ℕ → ℤ,
      (a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
        a n = -∑ d ∈ n.properDivisors,
          (2 * ((n / d : ℕ) : ℤ) - (ArithmeticFunction.sigma 1 (n / d) : ℤ)) * a d) →
      (∀ n : ℕ, 1 ≤ n →
        ∑ d ∈ n.divisors, s d * (ArithmeticFunction.sigma 1 (n / d) : ℤ) =
          if n = 1 then 1 else 0) →
      (B 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → B n = 1 + ∑ d ∈ n.properDivisors, B d) →
      (H 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → H n = ∑ d ∈ n.properDivisors, H d) →
      (e 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
        e n = -∑ d ∈ n.properDivisors,
          (2 * (Nat.totient (n / d) : ℤ) - ((n / d : ℕ) : ℤ)) * e d) →
      ∀ n : ℕ, 1 ≤ n →
        a n = ∑ d ∈ n.divisors, s d * B (n / d) ∧
        a n = ∑ d ∈ n.divisors, ((d : ℤ) * ArithmeticFunction.moebius d) * H (n / d) ∧
        a n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) * e (n / d) := by
  sorry

end OMA.S_oeis_a323910
