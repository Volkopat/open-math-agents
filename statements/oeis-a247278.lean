import Mathlib

/-!
# A247278: Least integer k > 0 such that k*n - prime(k) is a square

Source: https://oeis.org/A247278

Conjecture (Zhi-Wei Sun, OEIS A247278):
For every `n > 1` (i.e., `n ≥ 2`), there exists a positive integer `k` such that
`k * n - prime(k)` is a perfect square (so `a(n)` exists for all `n ≥ 2`).

Conventions:
- Offset: `2`; first terms: `a(2) = 2` (`2*2 - 3 = 1^2`), `a(3) = 1` (`1*3 - 2 = 1^2`),
  `a(4) = 4` (`4*4 - 7 = 3^2`), `a(5) = 29`, `a(6) = 1` (`1*6 - 2 = 2^2`), ...
- `nthPrime k` denotes the `k`-th prime (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`).
- Writing `k * n = nthPrime k + m ^ 2` in `ℕ` avoids subtraction underflow and guarantees
  `k * n ≥ prime(k)`.
-/

namespace OMA.S_oeis_a247278

/-- The `k`-th prime number (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- Conjecture: for every `n ≥ 2`, there exist `k ≥ 1` and `m : ℕ` such that
`k * n - prime(k) = m^2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ k m : ℕ, 1 ≤ k ∧ k * n = nthPrime k + m ^ 2 := by
  sorry

end OMA.S_oeis_a247278
