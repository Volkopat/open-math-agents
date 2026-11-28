import Mathlib

/-!
# OEIS A067182: Maximum of digitSum(F_n) - n Is 92 at n = 2619

Source: https://oeis.org/A067182
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $s(n)$ (OEIS A004090) denote the base-10 digit sum of the $n$-th Fibonacci number $F_n$.

Conjecture: The maximum of $s(n) - n$ over all $n \in \mathbb{N}$ is $92$, attained at
$n = 2619$. That is, $s(n) \le n + 92$ for all $n \in \mathbb{N}$ and $s(2619) = 2619 + 92$.
-/

namespace OMA.S_oeis_a067182

/-- Base-10 digit sum of a natural number. -/
def digitSum (m : ℕ) : ℕ :=
  (Nat.digits 10 m).sum

theorem main :
    (∀ n : ℕ, digitSum (Nat.fib n) ≤ n + 92) ∧
      digitSum (Nat.fib 2619) = 2619 + 92 := by
  sorry

end OMA.S_oeis_a067182
