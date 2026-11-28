import Mathlib

/-!
# OEIS A067843: Least k > n with phi(k - n) + phi(k + n) = phi(2k) Satisfies k ≥ n + 4

Source: https://oeis.org/A067843
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

For $n \ge 1$, let $a(n)$ be the least integer $k > n$ such that
$\phi(k - n) + \phi(k + n) = \phi(2k)$.

Conjecture (Robert Israel, 2018):
For every $n \ge 1$, $a(n) \ge n + 4$; that is, no integer $k$ with $n < k < n + 4$
satisfies $\phi(k - n) + \phi(k + n) = \phi(2k)$.
-/

namespace OMA.S_oeis_a067843

theorem main :
    ∀ n k : ℕ, 1 ≤ n → n < k →
      Nat.totient (k - n) + Nat.totient (k + n) = Nat.totient (2 * k) →
      n + 4 ≤ k := by
  sorry

end OMA.S_oeis_a067843
