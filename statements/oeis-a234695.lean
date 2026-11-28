import Mathlib

/-!
# A234695: Primes p with prime(p) - p + 1 also prime

Source: https://oeis.org/A234695

Conjecture (OEIS A234695, following the conjecture in A234694):
There are infinitely many primes `p` such that `prime(p) - p + 1` is also prime.

Conventions:
- Offset: `1`; first terms: `2` (`3 - 2 + 1 = 2`), `3` (`5 - 3 + 1 = 3`),
  `5` (`11 - 5 + 1 = 7`), `7` (`17 - 7 + 1 = 11`), `13` (`41 - 13 + 1 = 29`), ...
- `nthPrime n` denotes the `n`-th prime (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`).
- For every `n ≥ 1`, `nthPrime n > n`, so `nthPrime p - p` has no `ℕ` subtraction underflow.
-/

namespace OMA.S_oeis_a234695

/-- The `n`-th prime number (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- The set of primes `p` such that `prime(p) - p + 1` is also prime (OEIS A234695). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime (nthPrime p - p + 1)}

/-- Conjecture: there are infinitely many primes `p` with `prime(p) - p + 1` prime. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a234695
