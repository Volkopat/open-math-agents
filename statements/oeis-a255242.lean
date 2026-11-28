import Mathlib

/-!
OEIS A255242: Calculate the aliquot parts of a number n and take their sum. Then repeat the
process calculating the aliquot parts of all the previous aliquot parts and add their sum to
the previous one. Repeat the process until the sum to be added is zero.

Equivalently (formula of Chai Wah Wu, Mar 24 2026), a(1) = 0 and
a(n) = Sum_{d|n, d<n} (a(d) + d).

Formulas conjectured by Sequence Machine (Antti Karttunen, Nov 22 2024);
this file states three of them:
  (1) a(n) = (A191161(n) - n)/2, stated as 2*a(n) = A191161(n) - n;
  (2) a(n) = Sum_{d|n} A001065(d) * A074206(n/d);
  (3) a(n) = Sum_{d|n} A051953(d) * A067824(n/d).
Here
  A191161 (hypersigma): g(n) = sigma(n) + Sum_{d|n, d<n} g(d),
  A001065(n) = sigma(n) - n,
  A074206 (Kalmar's problem): H(1) = 1, H(n) = Sum_{d|n, d<n} H(d) for n > 1,
  A051953(n) = n - phi(n),
  A067824: B(1) = 1, B(n) = 1 + Sum_{d|n, d<n} B(d) for n > 1.
-/

namespace OMA.S_oeis_a255242

theorem main :
    ∀ a g H B : ℕ → ℤ,
      (∀ n : ℕ, 1 ≤ n → a n = ∑ d ∈ n.properDivisors, (a d + d)) →
      (∀ n : ℕ, 1 ≤ n →
        g n = (ArithmeticFunction.sigma 1 n : ℤ) + ∑ d ∈ n.properDivisors, g d) →
      (H 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → H n = ∑ d ∈ n.properDivisors, H d) →
      (B 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → B n = 1 + ∑ d ∈ n.properDivisors, B d) →
      ∀ n : ℕ, 1 ≤ n →
        2 * a n = g n - n ∧
        a n = ∑ d ∈ n.divisors,
          ((ArithmeticFunction.sigma 1 d : ℤ) - d) * H (n / d) ∧
        a n = ∑ d ∈ n.divisors, ((d : ℤ) - (Nat.totient d : ℤ)) * B (n / d) := by
  sorry

end OMA.S_oeis_a255242
