import Mathlib

/-!
# A182332: Primes of the form k^3 + k - 1

Source: https://oeis.org/A182332

Conjecture (OEIS A182332, implied by Bunyakovsky's conjecture):
There are infinitely many primes of the form `k^3 + k - 1` for `k ≥ 1`.

Conventions:
- Offset: `1`; first terms: `29` (`k = 3`), `67` (`k = 4`), `349` (`k = 7`),
  `1009` (`k = 10`), `3389` (`k = 15`), `4111` (`k = 16`), ...
- Requiring `1 ≤ k` ensures `k^3 + k ≥ 2` and avoids `ℕ` subtraction underflow.
-/

namespace OMA.S_oeis_a182332

/-- The set of primes of the form `k^3 + k - 1` with `k ≥ 1` (OEIS A182332). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ∃ k : ℕ, 1 ≤ k ∧ p = k ^ 3 + k - 1}

/-- Conjecture: there are infinitely many primes of the form `k^3 + k - 1`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a182332
