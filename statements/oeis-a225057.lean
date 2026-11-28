import Mathlib

/-!
# A225057: Least prime p such that p * 6^n - 1 and p * 6^n + 1 are primes

Source: https://oeis.org/A225057

Conjecture (OEIS A225057, implied by Dickson's conjecture):
For every `n ≥ 1`, there exists a prime `p` such that both `p * 6^n - 1` and `p * 6^n + 1`
are prime (so `a(n)` exists for all `n ≥ 1`).

Conventions:
- Offset: `1`; first terms: `a(1) = 2` (`11, 13`), `a(2) = 2` (`71, 73`), `a(3) = 2`
  (`431, 433`), `a(4) = 2`, `a(5) = 47`, `a(6) = 3`, ...
- For `n = 0`, no prime `p` satisfies `p - 1` and `p + 1` both prime, hence `1 ≤ n`.
-/

namespace OMA.S_oeis_a225057

/-- Conjecture: for every `n ≥ 1`, there exists a prime `p` such that `p * 6^n - 1` and
`p * 6^n + 1` are both prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p * 6 ^ n - 1) ∧ Nat.Prime (p * 6 ^ n + 1) := by
  sorry

end OMA.S_oeis_a225057
