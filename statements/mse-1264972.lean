import Mathlib

/-!
# Rationality of the series $\sum_{n=0}^{\infty} \frac{1}{n^2 + 2an + b}$

Source: https://math.stackexchange.com/questions/1264972/is-it-true-that-sum-n-0-infty-frac1n22anb-in-bbb-q-iff-exists-k
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Given two positive integers $a$ and $b$, is it true that
$$\sum_{n=0}^{\infty} \frac{1}{n^2 + 2an + b} \in \mathbb{Q}
  \iff \exists k \in \mathbb{N}^+ \text{ such that } a^2 - b = k^2?$$
-/

namespace OMA.S_mse_1264972

theorem main :
    ∀ a b : ℕ, 0 < a → 0 < b →
      ((∃ q : ℚ,
          HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2 + 2 * (a : ℝ) * (n : ℝ) + (b : ℝ))) (q : ℝ)) ↔
        ∃ k : ℕ, 0 < k ∧ (a : ℤ) ^ 2 - (b : ℤ) = (k : ℤ) ^ 2) := by
  sorry

end OMA.S_mse_1264972
