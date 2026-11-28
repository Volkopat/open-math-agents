import Mathlib

/-!
# A248626: Least positive integer m such that prime(m + n) divides 2^m - 1

Source: https://oeis.org/A248626

Conjecture (Zhi-Wei Sun, OEIS A248626):
For every `n ≥ 1`, there exists a positive integer `m` such that `prime(m + n)` divides
`2^m - 1` (so `a(n)` exists for all `n ≥ 1`).

Conventions:
- Offset: `1`; first terms: `a(1) = 3` (`prime(4) = 7 ∣ 2^3 - 1`),
  `a(2) = 22` (`prime(24) = 89 ∣ 2^22 - 1`), `a(3) = 18` (`prime(21) = 73 ∣ 2^18 - 1`),
  `a(4) = 50`, `a(5) = 48`, `a(6) = 5` (`prime(11) = 31 ∣ 2^5 - 1`), ...
- `nthPrime k` denotes the `k`-th prime (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`).
-/

namespace OMA.S_oeis_a248626

/-- The `k`-th prime number (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- Conjecture: for every `n ≥ 1`, there exists `m ≥ 1` such that `prime(m + n) ∣ 2^m - 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ nthPrime (m + n) ∣ (2 ^ m - 1) := by
  sorry

end OMA.S_oeis_a248626
