import Mathlib

/-!
# A375180: a(n) = Sum_{k = 0..n-1} (-1)^(n+k+1)*binomial(3*n, k)^3

Source: https://oeis.org/A375180

The entry (Peter Bala, Aug 2024) makes four conjectures, stated together here:

1. `a(p) == 1 (mod p^5)` for all primes `p >= 7`;
2. for `r >= 2` and prime `p >= 5`, `a(p^r) == a(p^(r-1)) (mod p^(3*r+3))`;
3. more generally, for a positive integer `m` and
   `b_m(n) = Sum_{k = 0..n-1} (-1)^(n+k+1)*binomial(3*n, k)^(2*m+1)`,
   `b_m(p) == 1 (mod p^(2*m+3))` for all primes `p >= 2*m + 5`;
4. and for `r >= 2`, `b_m(p^r) == b_m(p^(r-1)) (mod p^(3*r+2*m+1))` for all primes `p >= 2*m + 5`.

A congruence `x == y (mod N)` between integers is written as `N ∣ x - y`.
-/

namespace OMA.S_oeis_a375180

/-- A375180: `a(n) = Sum_{k = 0..n-1} (-1)^(n+k+1) * binomial(3*n, k)^3`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-1 : ℤ) ^ (n + k + 1) * ((3 * n).choose k : ℤ) ^ 3

/-- The family of the entry: `b m n = Sum_{k = 0..n-1} (-1)^(n+k+1) * binomial(3*n, k)^(2*m+1)`. -/
def b (m n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (-1 : ℤ) ^ (n + k + 1) * ((3 * n).choose k : ℤ) ^ (2 * m + 1)

/-- The four conjectured supercongruences of the entry. -/
theorem main :
    (∀ p : ℕ, p.Prime → 7 ≤ p → ((p : ℤ) ^ 5) ∣ (a p - 1)) ∧
    (∀ p r : ℕ, p.Prime → 5 ≤ p → 2 ≤ r →
      ((p : ℤ) ^ (3 * r + 3)) ∣ (a (p ^ r) - a (p ^ (r - 1)))) ∧
    (∀ m p : ℕ, 1 ≤ m → p.Prime → 2 * m + 5 ≤ p → ((p : ℤ) ^ (2 * m + 3)) ∣ (b m p - 1)) ∧
    (∀ m p r : ℕ, 1 ≤ m → p.Prime → 2 * m + 5 ≤ p → 2 ≤ r →
      ((p : ℤ) ^ (3 * r + 2 * m + 1)) ∣ (b m (p ^ r) - b m (p ^ (r - 1)))) := by
  sorry

end OMA.S_oeis_a375180
