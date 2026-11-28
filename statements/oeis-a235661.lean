import Mathlib

/-!
# A235661: Primes p with p*(p + 1) - prime(p) prime

Source: https://oeis.org/A235661

Conjecture (OEIS A235661, following the conjecture in A232353):
There are infinitely many primes `p` such that `p * (p + 1) - prime(p)` is prime.

Conventions:
- Offset: `1`; first terms: `2` (`6 - 3 = 3`), `3` (`12 - 5 = 7`),
  `5` (`30 - 11 = 19`), `11` (`132 - 31 = 101`), `19` (`380 - 67 = 313`), ...
- `nthPrime n` denotes the `n`-th prime (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`).
- We include `nthPrime p < p * (p + 1)` explicitly to prevent `ℕ` subtraction underflow.
-/

namespace OMA.S_oeis_a235661

/-- The `n`-th prime number (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- The set of primes `p` such that `p * (p + 1) - prime(p)` is prime (OEIS A235661). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ nthPrime p < p * (p + 1) ∧ Nat.Prime (p * (p + 1) - nthPrime p)}

/-- Conjecture: there are infinitely many primes `p` with `p * (p + 1) - prime(p)` prime. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a235661
