import Mathlib

/-!
# A253178: Least k >= 1 such that 2 * A007494(n)^k + 1 is prime

Source: https://oeis.org/A253178

Conjecture (OEIS A253178):
`a(n)` is defined for every `n ≥ 1`; that is, for every `n ≥ 1`, there exists `k ≥ 1`
such that `2 * A007494(n)^k + 1` is prime, where `A007494(n) = ⌈3n / 2⌉` enumerates the
nonnegative integers congruent to `0` or `2` modulo `3`.

Conventions:
- Offset: `1`; `A007494(n) = (3 * n + 1) / 2` gives `2, 3, 5, 6, 8, 9, 11, 12, ...` for
  `n = 1, 2, 3, ...`.
- First terms of A253178: `1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 47, 1, 1, 1, 1, ...`
  (for `n = 8`, `A007494(8) = 12` and `2 * 12^3 + 1 = 3457` is prime).
-/

namespace OMA.S_oeis_a253178

/-- The `n`-th term of OEIS A007494 (`⌈3n / 2⌉`, giving `0, 2, 3, 5, 6, 8, 9, ...`). -/
def a007494 (n : ℕ) : ℕ :=
  (3 * n + 1) / 2

/-- Conjecture: for every `n ≥ 1`, there exists `k ≥ 1` such that
`2 * A007494(n)^k + 1` is prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ Nat.Prime (2 * (a007494 n) ^ k + 1) := by
  sorry

end OMA.S_oeis_a253178
