import Mathlib

/-!
# A006532: Infinitely Many Numbers Whose Sum of Divisors Is a Square

Source: https://oeis.org/A006532
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

A006532 consists of positive integers `n` whose sum of divisors `σ(n)` is a perfect square.

Conjecture (implied by Bunyakovsky's conjecture): There are infinitely many positive integers `n`
such that `σ(n)` is a perfect square.
-/

namespace OMA.S_oeis_a006532

theorem main :
    Set.Infinite { n : ℕ | 0 < n ∧ IsSquare (ArithmeticFunction.sigma 1 n) } := by
  sorry

end OMA.S_oeis_a006532
