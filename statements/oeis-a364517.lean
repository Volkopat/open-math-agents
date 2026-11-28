import Mathlib

/-!
# A364517: a(n) = (5/7) * (9n)! (7n/2)!^2 / ((9n/2)! (7n)! (5n/2)! n!^2) for n >= 1, a(0) = 1

Source: https://oeis.org/A364517

Offset 0. The name uses fractional factorials (gamma function). The entry gives the
equivalent integer formula
  a(n) = Sum_{k = 0..n} binomial(7n - 1, n - k)^2 * binomial(5n + k - 2, k),
which is used here as the definition (it reproduces the data 1, 40, 7650, 1847560, ...).

Conjecture (formula section of the entry, 2023): the supercongruences
  a(n p^r) == a(n p^(r-1)) (mod p^(3r))
hold for all primes p >= 5 and all positive integers n and r.

Formalized: a(n) is an integer; for n = 0 it is set to 1 explicitly (for n >= 1 no
natural-number subtraction truncates, since 7n - 1 >= 0 and 5n + k - 2 >= 0). The
congruence is written as divisibility in the integers, `p^(3r) ∣ a(n p^r) - a(n p^(r-1))`.
-/

namespace OMA.S_oeis_a364517

/-- A364517 via the binomial sum of the entry, with a(0) = 1. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 1 else
    ∑ k ∈ Finset.range (n + 1),
      ((Nat.choose (7 * n - 1) (n - k) : ℤ) ^ 2 * (Nat.choose (5 * n + k - 2) k : ℤ))

/-- The conjectured supercongruences of the entry. -/
theorem main :
    ∀ p n r : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < r →
      ((p : ℤ) ^ (3 * r)) ∣ (a (n * p ^ r) - a (n * p ^ (r - 1))) := by
  sorry

end OMA.S_oeis_a364517
