import Mathlib

/-!
# OEIS A066868: Primes as n Plus Partial Sums of Safe Primes

Source: https://oeis.org/A066868
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $q_1 < q_2 < \cdots$ be the sequence of safe primes (OEIS A005385), i.e., primes $p$
such that $(p - 1)/2$ is also prime (equivalently $p = 2r + 1$ with $p, r$ both prime).

Conjecture: For every $n \in \mathbb{N}$, there exists $k \ge 1$ such that
$$n + \sum_{i=1}^{k} q_i$$
is prime.
-/

namespace OMA.S_oeis_a066868

/-- A prime `p` is a safe prime if `p = 2 * r + 1` for some prime `r`. -/
def IsSafePrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ r : ℕ, Nat.Prime r ∧ p = 2 * r + 1

theorem main :
    ∀ n : ℕ, ∃ k : ℕ, 1 ≤ k ∧
      Nat.Prime (n + ∑ i ∈ Finset.range k, Nat.nth IsSafePrime i) := by
  sorry

end OMA.S_oeis_a066868
