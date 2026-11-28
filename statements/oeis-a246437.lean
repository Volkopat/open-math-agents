import Mathlib

/-!
# A246437: Expansion of (1/2)*(1/(x+1)+1/(sqrt(-3*x^2-2*x+1)))

Source: https://oeis.org/A246437

Offset 0. Since 1/(1+x) = Sum (-1)^n x^n and 1/sqrt(1-2x-3x^2) = Sum T(n) x^n with
T(n) = Sum_{k} binomial(n,2k)*binomial(2k,k) (central trinomial coefficients, A002426),
a(n) = ((-1)^n + T(n))/2.

Peter Bala, Jan 07 2022, states (as known) the Gauss congruences
a(n*p^k) == a(n*p^(k-1)) (mod p^k) for all primes p; that part is not the target.
Conjecture (Peter Bala, Jan 07 2022): a(n*p^k) == a(n*p^(k-1)) (mod p^(2*k)) for primes
p >= 5 and positive integers n and k.

Formalized: a(n) : ℤ is ((-1)^n + T(n)) / 2 with integer division; the sum (-1)^n + T(n)
is always even (T(n) is odd for every n; checked numerically, and the quotient reproduces the data
1, 0, 2, 3, 10, 25, 71, 196, 554, 1569, 4477, 12826, 36895, 106470, 308114, 893803), so the
division is exact. The congruence is written as divisibility of the difference in ℤ by
(p : ℤ)^(2*k), for n ≥ 1, k ≥ 1, p prime with p ≥ 5.
-/

namespace OMA.S_oeis_a246437

/-- Central trinomial coefficient: coefficient of x^n in 1/sqrt(1-2x-3x^2). -/
def T (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1), ((Nat.choose n (2 * k) * Nat.choose (2 * k) k : ℕ) : ℤ)

/-- A246437: coefficient of x^n in (1/2)*(1/(1+x) + 1/sqrt(1-2x-3x^2)). -/
def a (n : ℕ) : ℤ := ((-1 : ℤ) ^ n + T n) / 2

theorem main : ∀ p n k : ℕ, p.Prime → 5 ≤ p → 1 ≤ n → 1 ≤ k →
    (p : ℤ) ^ (2 * k) ∣ a (n * p ^ k) - a (n * p ^ (k - 1)) := by
  sorry

end OMA.S_oeis_a246437
