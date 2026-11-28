import Mathlib

/-!
# OEIS A068704: Prime Concatenation of Powers n^k, n^(k-1), ..., n, 1

Source: https://oeis.org/A068704
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

For a positive integer $n \ge 1$ and $k \ge 1$, form the base-10 concatenation of
$n^k, n^{k-1}, \ldots, n^2, n, 1$ (in that order from most significant to least significant).

Conjecture: For every $n \ge 1$, there exists $k \ge 1$ such that the resulting
concatenation is prime.
-/

namespace OMA.S_oeis_a068704

/-- Base-10 concatenation of two natural numbers `a` followed by `b` (for `b ≥ 1`). -/
def concat10 (a b : ℕ) : ℕ :=
  a * 10 ^ (Nat.digits 10 b).length + b

/-- Base-10 concatenation of `n^k, n^(k-1), ..., n, 1`. -/
def powerConcat (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => concat10 (n ^ (k + 1)) (powerConcat n k)

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ Nat.Prime (powerConcat n k) := by
  sorry

end OMA.S_oeis_a068704
