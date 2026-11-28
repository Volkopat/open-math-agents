import Mathlib

/-!
# A239579: Number of k in {1..n} such that prime(prime(prime(k*n))) - 2 is prime

Source: https://oeis.org/A239579

Conjecture (OEIS A239579):
For every `n > 9`, `a(n) > 0`; that is, there exists `k` with `1 ≤ k ≤ n` such
that `prime(prime(prime(k * n))) - 2` is prime.

Conventions:
- Offset: `1`; first terms: `1, 0, 1, 0, 0, 2, 3, 2, 0, 3, 1, 2, 2, 3, 2, ...`
  (last zero at `n = 9`).
- `nthPrime m` is the `m`-th prime (`1`-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...),
  defined via `Nat.nth Nat.Prime (m - 1)`.
-/

namespace OMA.S_oeis_a239579

/-- The `m`-th prime number (`1`-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- Conjecture: for every `n > 9`, there exists `1 ≤ k ≤ n` such that
`prime(prime(prime(k * n))) - 2` is prime. -/
theorem main :
    ∀ n : ℕ, 9 < n →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ Nat.Prime (nthPrime (nthPrime (nthPrime (k * n))) - 2) := by
  sorry

end OMA.S_oeis_a239579
