import Mathlib

/-!
# A216266: Number of primes between n^3 and n^3 + n (inclusive)

Source: https://oeis.org/A216266

Conjecture (OEIS A216266):
For every `n > 23`, there is at least one prime `p` with `n^3 ≤ p ≤ n^3 + n`
(i.e., `a(n) > 0`).

Conventions:
- Offset: `1`; first terms: `a(1) = 1`, `a(2) = 0`, `a(3) = 1`, ..., `a(23) = 0`,
  `a(24) = 3`, `a(25) = 5`, ...
- Computed as the cardinality of `(Finset.Icc (n ^ 3) (n ^ 3 + n)).filter Nat.Prime`.
-/

namespace OMA.S_oeis_a216266

/-- Number of primes in the closed interval `[n^3, n^3 + n]` (OEIS A216266). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc (n ^ 3) (n ^ 3 + n)).filter Nat.Prime).card

/-- Conjecture: `a(n) > 0` for all `n > 23`. -/
theorem main :
    ∀ n : ℕ, 23 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a216266
