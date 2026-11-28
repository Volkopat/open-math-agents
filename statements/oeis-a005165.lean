import Mathlib

/-!
# OEIS A005165 (alternating factorials): smallest prime divisor conjecture

Source: https://oeis.org/A005165
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Gerald McGarvey, in the entry): for `n > 2`, the smallest prime divisor of `a(n)`
exceeds `n`, where `a(n) = n! - (n-1)! + (n-2)! - ⋯ ± 1!` (with `a(0) = 0`).

(The entry's second, lattice-path conjecture is a different item; this file states the first.)
Recursion used: `a(0) = 0`, `a(n+1) = (n+1)! - a(n)`.
-/

namespace OMA.S_oeis_a005165

/-- Alternating factorials. -/
def a : ℕ → ℕ
  | 0 => 0
  | (n + 1) => (n + 1).factorial - a n

/-- McGarvey's conjecture. -/
theorem main : ∀ n : ℕ, 2 < n → n < (a n).minFac := by
  sorry

end OMA.S_oeis_a005165
