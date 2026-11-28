import Mathlib

/-!
# A275654: a(n) = (5n)!/((3n)! n!^2) * ((3n/2)! (7n/2)!)/(5n/2)!^2

Source: https://oeis.org/A275654

Offset 0; terms 1, 28, 2646, 316540, 42031990, ...
The entry also gives (Peter Bala, Mar 23 2022)
a(n) = Sum_{k = 0..n} binomial(4n-k-1, n-k) * binomial(5n, k)^2,
and states a(p) == a(1) (mod p^3) for primes p >= 5 (not part of the target).
Conjecture (Peter Bala, Mar 23 2022): the supercongruences
a(n p^k) == a(n p^(k-1)) (mod p^(3k)) hold for all primes p >= 5 and all
positive integers n and k.

Formalized: a(n) is defined by Bala's binomial sum (an integer formula given in
the entry, avoiding half-integer factorials), as a natural number cast to ℤ.
For n >= 1 the upper argument 4n-k-1 is at least 3n-1, so natural subtraction
does not truncate; at n = 0 it gives a(0) = 1. Checked against the first 14
terms. The congruence is stated in ℤ with Int.ModEq.
-/

namespace OMA.S_oeis_a275654

/-- a(n) = Sum_{k = 0..n} binomial(4n-k-1, n-k) * binomial(5n, k)^2. -/
def a (n : ℕ) : ℤ :=
  ((Finset.range (n + 1)).sum fun k =>
    Nat.choose (4 * n - k - 1) (n - k) * Nat.choose (5 * n) k ^ 2 : ℕ)

theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD ((p : ℤ) ^ (3 * k))] := by
  sorry

end OMA.S_oeis_a275654
