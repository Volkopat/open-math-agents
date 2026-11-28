import Mathlib

/-!
# A247893: Least integer k > 0 such that prime(k) - k*n is a square

Source: https://oeis.org/A247893

Conjecture (Zhi-Wei Sun, OEIS A247893):
For every `n ≥ 1`, there exists a positive integer `k` such that `prime(k) - k * n`
is a perfect square (so `a(n)` exists for all `n ≥ 1`).

Conventions:
- Offset: `1`; first terms: `a(1) = 1` (`2 - 1 = 1^2`), `a(2) = 5` (`11 - 10 = 1^2`),
  `a(3) = 12` (`37 - 36 = 1^2`), `a(4) = 35` (`149 - 140 = 3^2`), `a(5) = 75`, ...
- `nthPrime k` denotes the `k`-th prime (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`).
- Writing `nthPrime k = k * n + m ^ 2` in `ℕ` avoids subtraction underflow and guarantees
  `prime(k) ≥ k * n`.
-/

namespace OMA.S_oeis_a247893

/-- The `k`-th prime number (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- Conjecture: for every `n ≥ 1`, there exist `k ≥ 1` and `m : ℕ` such that
`prime(k) - k * n = m^2`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k m : ℕ, 1 ≤ k ∧ nthPrime k = k * n + m ^ 2 := by
  sorry

end OMA.S_oeis_a247893
