import Mathlib

/-!
# OEIS A067567: Partition Convolution Divisibility and Parity (Bala's Conjecture)

Source: https://oeis.org/A067567
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $p(k)$ denote the number of partitions of $k$, and for $m \ge 1$ define
$$b_m(n) = \sum_{k=1}^{n} k^{2m+1} p(k)\, p(n - k).$$

Conjecture (Peter Bala, 2025): For every $m \ge 1$:
1. For every odd $n \ge 1$, $n \mid b_m(n)$.
2. For every $n \ge 1$, $n \mid b_m(2n)$, and $b_m(2n) / n$ is odd if and only if
   $n$ is odd and $p(n)$ is odd (i.e., $n$ belongs to OEIS A067567).
-/

namespace OMA.S_oeis_a067567

/-- Number of integer partitions of `k`. -/
def p (k : ℕ) : ℕ :=
  Fintype.card (Nat.Partition k)

/-- `b m n = ∑_{k=1..n} k^(2m+1) * p(k) * p(n - k)`. -/
def b (m n : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc 1 n, k ^ (2 * m + 1) * p k * p (n - k)

theorem main :
    ∀ m : ℕ, 1 ≤ m →
      (∀ n : ℕ, 1 ≤ n → Odd n → n ∣ b m n) ∧
      (∀ n : ℕ, 1 ≤ n →
        n ∣ b m (2 * n) ∧ (Odd (b m (2 * n) / n) ↔ Odd n ∧ Odd (p n))) := by
  sorry

end OMA.S_oeis_a067567
