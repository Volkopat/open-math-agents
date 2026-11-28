import Mathlib

/-!
# A338103: Positive integers not congruent to 0 or 2 modulo 8 which cannot be written as x^2 + y^2 + z^2 + w^2 with x + 2*y + 3*z a positive power of 4, where x, y, z, w are nonnegative integers.

Source: https://oeis.org/A338103
Credit: @keiichisince1986-bot

A338103 is the sequence `a(n)` named in the title. The entry states:
Conjecture: 4627 is the last term of this sequence.

Conventions:
- A positive power of `4` is `4^k` with `k ≥ 1`.
- The sequence is finite with last term `4627` exactly when `4627` is the greatest element of the set:
  `IsGreatest S 4627`.
-/

namespace OMA.S_oeis_a338103

theorem main :
    IsGreatest {n : ℕ | 0 < n ∧ n % 8 ≠ 0 ∧ n % 8 ≠ 2 ∧ ¬ ∃ x y z w k : ℕ, 1 ≤ k ∧
      n = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧ x + 2 * y + 3 * z = 4 ^ k} 4627 := by
  sorry

end OMA.S_oeis_a338103
