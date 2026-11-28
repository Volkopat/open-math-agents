import Mathlib

/-!
# A015762: Numbers n such that phi(n) | sigma_4(n)

Source: https://oeis.org/A015762
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
Whenever a positive integer `n` satisfies `φ(n) ∣ σ₄(n)`, we have
`φ(n) ∣ σ_{8j + 4}(n)` for all `j : ℕ`.

Conventions:
- `Nat.totient` is Euler's totient function `φ`.
- `ArithmeticFunction.sigma k n` is the sum of `k`-th powers of positive divisors of `n`.
-/

namespace OMA.S_oeis_a015762

theorem main :
    ∀ n : ℕ, n ≥ 1 →
      Nat.totient n ∣ ArithmeticFunction.sigma 4 n →
      ∀ j : ℕ, Nat.totient n ∣ ArithmeticFunction.sigma (8 * j + 4) n := by
  sorry

end OMA.S_oeis_a015762
