import Mathlib

/-!
# OEIS A038711: Fortune's Conjecture (Primorial + m Prime)

Source: https://oeis.org/A038711
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $P_n = \prod_{i=1}^{n} p_i$ be the $n$-th primorial (product of the first $n$ primes),
and let $a(n)$ be the smallest integer $m \ge 1$ such that $P_n + m$ is prime.

Fortune's Conjecture: No term $a(n)$ is composite (i.e., for every $n \ge 1$, $a(n)$ is
either $1$ or prime; equivalently, for $m > 1$ minimal with $P_n + m$ prime, $m$ is prime).
-/

namespace OMA.S_oeis_a038711

/-- The `n`-th primorial `p_1 * p_2 * ... * p_n`. -/
noncomputable def primorial (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- `IsLeastPrimeOffset n m` holds when `m ≥ 1` is minimal with `primorial n + m` prime. -/
def IsLeastPrimeOffset (n m : ℕ) : Prop :=
  1 ≤ m ∧ Nat.Prime (primorial n + m) ∧
    ∀ k, 1 ≤ k → k < m → ¬ Nat.Prime (primorial n + k)

theorem main :
    ∀ n m : ℕ, 1 ≤ n → IsLeastPrimeOffset n m → m = 1 ∨ Nat.Prime m := by
  sorry

end OMA.S_oeis_a038711
