import Mathlib

/-!
# A242802: Number of primes p < n such that n - p is a term of A242754

Source: https://oeis.org/A242802
Author: Zhi-Wei Sun (2014)

Conjecture (Zhi-Wei Sun, OEIS A242802):
For every integer `n > 3`, `a(n) > 0`; that is, there exists a prime `p < n` such
that `k = n - p` belongs to OEIS A242754 (meaning `k ≥ 1` and the unique modular
inverse `q ∈ {1, ..., prime(k) - 1}` of `k` modulo `prime(k)` is prime).

Conventions:
- Offset: `1`; first terms of A242802: `0, 0, 0, 1, 2, 2, 2, 2, 4, 2, 2, 2, 4, ...`.
- `nthPrime k = Nat.nth Nat.Prime (k - 1)` is the `1`-indexed `k`-th prime.
-/

namespace OMA.S_oeis_a242802

/-- The `k`-th prime number (`1`-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- Predicate for membership in OEIS A242754: `k ≥ 1` and the modular inverse of `k`
modulo `prime(k)` in `{1, ..., prime(k) - 1}` is prime. -/
def InA242754 (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ q : ℕ, Nat.Prime q ∧ q < nthPrime k ∧ (k * q) % nthPrime k = 1

/-- Conjecture (Zhi-Wei Sun): for every `n > 3`, there is a prime `p < n` such that
`n - p` belongs to A242754. -/
theorem main :
    ∀ n : ℕ, 3 < n → ∃ p : ℕ, Nat.Prime p ∧ p < n ∧ InA242754 (n - p) := by
  sorry

end OMA.S_oeis_a242802
