import Mathlib

/-!
# A022462: a(n) = prime(n) * prime(n+2) mod prime(n+1)

Source: https://oeis.org/A022462
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
For 1-indexed primes `prime(1) = 2, prime(2) = 3, ...`, let
`a(n) = (prime(n) * prime(n + 2)) mod prime(n + 1)`.
Then for all `n ≥ 1` except `n = 3` and `n = 8`:
  `a(n) = prime(n) * prime(n + 2) - prime(n + 1) * (prime(n) + prime(n + 2) - prime(n + 1) - 1)`.

Conventions:
- `nthPrime1 n` is `Nat.nth Nat.Prime (n - 1)`, so `nthPrime1 1 = 2`, `nthPrime1 2 = 3`, etc.
- The equality is stated in `ℤ` to avoid natural-number truncation in subtraction.
-/

namespace OMA.S_oeis_a022462

noncomputable def nthPrime1 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

theorem main :
    ∀ n : ℕ, n ≥ 1 → n ≠ 3 → n ≠ 8 →
      ((nthPrime1 n * nthPrime1 (n + 2) % nthPrime1 (n + 1) : ℕ) : ℤ) =
        (nthPrime1 n : ℤ) * (nthPrime1 (n + 2) : ℤ) -
          (nthPrime1 (n + 1) : ℤ) *
            ((nthPrime1 n : ℤ) + (nthPrime1 (n + 2) : ℤ) - (nthPrime1 (n + 1) : ℤ) - 1) := by
  sorry

end OMA.S_oeis_a022462
