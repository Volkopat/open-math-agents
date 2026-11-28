import Mathlib

/-!
# A103795: Minimal base b such that (b^prime(n) + 1) / (b + 1) is prime

Source: https://oeis.org/A103795

Conjecture (OEIS A103795):
The sequence is defined for every `n ≥ 2`; that is, for every odd prime `p = prime(n)`,
there exists an integer base `b ≥ 2` such that `(b^p + 1) / (b + 1)` is prime.

Conventions:
- Offset: `2`; first terms: `a(2) = 2` (`(2^3 + 1)/3 = 3`), `a(3) = 2` (`(2^5 + 1)/3 = 11`),
  `a(4) = 2`, `a(5) = 2`, `a(6) = 2`, `a(7) = 2`, `a(8) = 2`, `a(9) = 2`, `a(10) = 7`, ...
- `nthPrime n` denotes the `n`-th prime (1-indexed: `nthPrime 2 = 3`, `nthPrime 3 = 5`).
- For odd prime `p`, `(b + 1)` always divides `b^p + 1`; we state divisibility explicitly.
-/

namespace OMA.S_oeis_a103795

/-- The `n`-th prime number (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- Conjecture: for every `n ≥ 2`, there exists `b ≥ 2` such that
`(b^(prime(n)) + 1) / (b + 1)` is prime. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ∃ b : ℕ, 2 ≤ b ∧ (b + 1) ∣ (b ^ nthPrime n + 1) ∧
        Nat.Prime ((b ^ nthPrime n + 1) / (b + 1)) := by
  sorry

end OMA.S_oeis_a103795
