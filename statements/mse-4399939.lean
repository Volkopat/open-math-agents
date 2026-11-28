import Mathlib

/-!
# Eventual unimodality of powers of positive-coefficient polynomials

Source: https://math.stackexchange.com/questions/4399939/prove-or-disprove-that-the-power-of-positive-term-polynomial-will-be-eventually
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $P(x) = \sum_{i=0}^n a_i x^i \in \mathbb{R}[x]$ be a polynomial such that $a_i > 0$ for
every $0 \le i \le n$. Does there always exist a positive integer $r$ such that
$P(x)^r = \sum_{i=0}^{nr} b_i x^i$ is unimodal, i.e. there exists $0 \le j \le nr$ such that
$b_0 \le b_1 \le \dots \le b_j$ and $b_{j+1} \ge \dots \ge b_{nr}$?
-/

namespace OMA.S_mse_4399939

theorem main :
    ∀ (n : ℕ) (P : Polynomial ℝ),
      P.natDegree = n →
      (∀ i ≤ n, 0 < P.coeff i) →
      ∃ r : ℕ, 0 < r ∧
        ∃ j ≤ n * r,
          (∀ i, i < j → (P ^ r).coeff i ≤ (P ^ r).coeff (i + 1)) ∧
          (∀ i, j + 1 ≤ i → i < n * r → (P ^ r).coeff (i + 1) ≤ (P ^ r).coeff i) := by
  sorry

end OMA.S_mse_4399939
