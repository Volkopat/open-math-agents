import Mathlib

/-!
# A275652: a(n) = binomial(3n,3n/2)*binomial(2n,n)*binomial(5n/2,n/2)/binomial(n,n/2)

Source: https://oeis.org/A275652

Offset 0; terms 1, 10, 300, 11440, 485100, ...
Peter Bala (Mar 22 2022) gives the formula
a(n) = Sum_{k = 0..n} binomial(2*n-k-1,n-k)*binomial(3*n,k)^2
and states (as known) a(p) == a(1) (mod p^3) for primes p >= 5. He conjectures:
the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) hold for all primes
p >= 5 and all positive integers n and k.

Formalized: a(n) is defined in ℤ through Bala's binomial sum (the name uses
half-integer binomials, i.e. Gamma quotients, for odd n; the sum agrees with
all listed terms). In ℕ, 2*n-k-1 truncates only at n = 0, k = 0, where
binomial(0,0) = 1 = a(0) as required. The congruence is stated as
Int.ModEq modulo p^(3k), for p prime, p >= 5, n >= 1, k >= 1.
The statement a(p) == a(1) (mod p^3) is presented as known and is the case
n = 1, k = 1 of the target.
-/

namespace OMA.S_oeis_a275652

/-- A275652 via Sum_{k=0..n} binomial(2n-k-1, n-k) * binomial(3n, k)^2. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    ((Nat.choose (2 * n - k - 1) (n - k) : ℤ) * (Nat.choose (3 * n) k : ℤ) ^ 2)

theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD ((p : ℤ) ^ (3 * k))] := by
  sorry

end OMA.S_oeis_a275652
