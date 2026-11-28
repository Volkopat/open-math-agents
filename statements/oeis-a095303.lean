import Mathlib

/-!
# A095303: Smallest number k such that k^n - 2 is prime

Source: https://oeis.org/A095303

Conjecture (OEIS A095303, implied by Bunyakovsky's conjecture):
For every `n ≥ 1`, there exists an integer `k ≥ 2` such that `k^n - 2` is prime,
so `a(n)` is well-defined for all `n ≥ 1`.

Conventions:
- Offset: `1`; first terms: `a(1) = 4` (`4^1 - 2 = 2`), `a(2) = 2` (`2^2 - 2 = 2`),
  `a(3) = 9` (`9^3 - 2 = 727`), `a(4) = 3` (`3^4 - 2 = 79`), `a(5) = 3`, `a(6) = 3`,
  `a(7) = 7`, `a(8) = 7`, `a(9) = 3`, `a(10) = 21`, ...
- Requiring `2 ≤ k` guarantees `k^n ≥ 2` for all `n ≥ 1`, avoiding `ℕ` subtraction underflow.
-/

namespace OMA.S_oeis_a095303

/-- Conjecture: for every `n ≥ 1`, there exists `k ≥ 2` such that `k^n - 2` is prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 2 ≤ k ∧ Nat.Prime (k ^ n - 2) := by
  sorry

end OMA.S_oeis_a095303
