import Mathlib

/-!
OEIS A101035: Dirichlet inverse of the gcd-sum function (A018804).

A018804(n) = Sum_{k=1..n} gcd(k, n). The sequence a is characterized by
Sum_{d|n} a(d) * A018804(n/d) = [n = 1] for all n >= 1.

Conjecture (Benedict W. J. Irwin, 2017): the logarithmic g.f. Sum_{m>=1} a(m) x^m / m equals
Sum_{n>0,k>0} mu(n)*mu(k)*log(1/(1-x^(n*k))).
Since log(1/(1-y)) = Sum_{j>=1} y^j / j, comparing the coefficients of x^m this says
a(m)/m = Sum over n*k*j = m of mu(n)*mu(k)/j, which is the statement below.
-/

namespace OMA.S_oeis_a101035

theorem main :
    ∀ a : ℕ → ℤ,
      (∀ n : ℕ, 1 ≤ n →
        ∑ d ∈ n.divisors, a d * ∑ k ∈ Finset.Icc 1 (n / d), ((Nat.gcd k (n / d) : ℕ) : ℤ) =
          if n = 1 then 1 else 0) →
      ∀ m : ℕ, 1 ≤ m →
        ((a m : ℚ) / m =
          ∑ n ∈ m.divisors, ∑ k ∈ (m / n).divisors,
            ((ArithmeticFunction.moebius n * ArithmeticFunction.moebius k : ℤ) : ℚ) /
              ((m / (n * k) : ℕ) : ℚ)) := by
  sorry

end OMA.S_oeis_a101035
