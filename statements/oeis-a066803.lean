import Mathlib

/-!
# OEIS A066803: gcd(2^(2^k) + 1, 3^(2^k) + 1) = 1 for k ≠ 1

Source: https://oeis.org/A066803
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $a(n) = \gcd(2^n + 1, 3^n + 1)$.

Conjecture: For every $k \in \mathbb{N}$ with $k \ne 1$,
$$a(2^k) = \gcd(2^{2^k} + 1, 3^{2^k} + 1) = 1.$$
-/

namespace OMA.S_oeis_a066803

theorem main :
    ∀ k : ℕ, k ≠ 1 → Nat.gcd (2 ^ (2 ^ k) + 1) (3 ^ (2 ^ k) + 1) = 1 := by
  sorry

end OMA.S_oeis_a066803
