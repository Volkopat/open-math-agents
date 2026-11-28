import Mathlib

/-!
# OEIS A031934: Consecutive Primes with Difference 16

Source: https://oeis.org/A031934
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Let $a(1) < a(2) < \cdots$ be the sequence of lower primes of pairs of consecutive
primes having a difference of $16$ (i.e., primes $p$ such that the next prime is $p + 16$).

Conjecture (Jahangeer Kholdi and Farideh Firoozbakht, 2014):
The sequence is infinite, and for every $n \ge 1$,
$$a(n+1) < a(n)^{1 + 1/n},$$
equivalently $a(n+1)^n < a(n)^{n+1}$ (so $a(n)^{1/n}$ is strictly decreasing).
-/

namespace OMA.S_oeis_a031934

/-- `IsGap16Prime p` holds when `p` and `p + 16` are consecutive primes. -/
def IsGap16Prime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + 16) ∧ ∀ q, p < q → q < p + 16 → ¬ Nat.Prime q

/-- The set of lower primes of consecutive prime pairs with gap 16. -/
def gap16Set : Set ℕ := {p | IsGap16Prime p}

theorem main :
    gap16Set.Infinite ∧
      ∀ n : ℕ, 1 ≤ n →
        (Nat.nth IsGap16Prime n) ^ n < (Nat.nth IsGap16Prime (n - 1)) ^ (n + 1) := by
  sorry

end OMA.S_oeis_a031934
