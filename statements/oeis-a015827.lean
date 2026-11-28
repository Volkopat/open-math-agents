import Mathlib

/-!
# A015827: Numbers k such that phi(k + 9) | sigma(k)

Source: https://oeis.org/A015827
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
There are infinitely many positive integers `k` such that `φ(k + 9) ∣ σ(k)`.

Conventions:
- `Nat.totient` is Euler's totient function `φ`.
- `ArithmeticFunction.sigma 1 k` is the sum of positive divisors `σ(k)`.
-/

namespace OMA.S_oeis_a015827

theorem main :
    Set.Infinite {k : ℕ | k ≥ 1 ∧ Nat.totient (k + 9) ∣ ArithmeticFunction.sigma 1 k} := by
  sorry

end OMA.S_oeis_a015827
