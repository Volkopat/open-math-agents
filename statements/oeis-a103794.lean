import Mathlib

/-!
# A103794: Smallest number b such that b^prime(n) - (b - 1)^prime(n) is prime

Source: https://oeis.org/A103794

Conjecture (OEIS A103794):
The sequence is defined for all positive indices `n ≥ 1`; that is, for every prime `p`,
there exists an integer `b ≥ 2` such that `b^p - (b - 1)^p` is prime.

Conventions:
- Offset: `1`; first terms: `a(1) = 2` (`2^2 - 1^2 = 3`), `a(2) = 2` (`2^3 - 1^3 = 7`),
  `a(3) = 2` (`2^5 - 1^5 = 31`), `a(4) = 2` (`2^7 - 1^7 = 127`),
  `a(5) = 6` (`6^11 - 5^11 = 313968931`), ...
- `nthPrime n` denotes the `n`-th prime (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`).
-/

namespace OMA.S_oeis_a103794

/-- The `n`-th prime number (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- Conjecture: for every `n ≥ 1`, there exists `b ≥ 2` such that
`b^(prime(n)) - (b - 1)^(prime(n))` is prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ b : ℕ, 2 ≤ b ∧ Nat.Prime (b ^ nthPrime n - (b - 1) ^ nthPrime n) := by
  sorry

end OMA.S_oeis_a103794
