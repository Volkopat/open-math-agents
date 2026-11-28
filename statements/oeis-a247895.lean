import Mathlib

/-!
# A247895: Least integer k > 0 such that prime(k) - k*n is prime

Source: https://oeis.org/A247895

Conjecture (Zhi-Wei Sun, OEIS A247895):
For every `n ≥ 1`, there exists a positive integer `k` such that `prime(k) - k * n`
is prime (so `a(n)` exists for all `n ≥ 1`).

Conventions:
- Offset: `1`; first terms: `a(1) = 3` (`5 - 3 = 2`), `a(2) = 7` (`17 - 14 = 3`),
  `a(3) = 13` (`41 - 39 = 2`), `a(4) = 31` (`127 - 124 = 3`), `a(5) = 69`, ...
- `nthPrime k` denotes the `k`-th prime (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`).
- Requiring `k * n < nthPrime k` avoids `ℕ` subtraction underflow.
-/

namespace OMA.S_oeis_a247895

/-- The `k`-th prime number (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- Conjecture: for every `n ≥ 1`, there exists `k ≥ 1` such that `prime(k) - k * n` is prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ k : ℕ, 1 ≤ k ∧ k * n < nthPrime k ∧ Nat.Prime (nthPrime k - k * n) := by
  sorry

end OMA.S_oeis_a247895
