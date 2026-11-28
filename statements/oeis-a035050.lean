import Mathlib

/-!
# OEIS A035050: Smallest k Such That k * 2^n + 1 Is Prime

Source: https://oeis.org/A035050
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $a(n)$ be the smallest positive integer $k$ such that $k \cdot 2^n + 1$ is prime.

Conjecture: For every $n \ge 1$, $a(n) < 2^n$ (so $a(n) \cdot 2^n + 1$ is a Proth prime).
Equivalently, for every $n \ge 1$, there exists $k$ with $1 \le k < 2^n$ such that
$k \cdot 2^n + 1$ is prime.
-/

namespace OMA.S_oeis_a035050

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ k < 2 ^ n ∧ Nat.Prime (k * 2 ^ n + 1) := by
  sorry

end OMA.S_oeis_a035050
