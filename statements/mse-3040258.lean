import Mathlib

/-!
# Two-variable function without separable series representation

Source: https://math.stackexchange.com/questions/3040258/is-there-any-two-variable-function-which-has-no-representation-of-the-form-sum
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Is there any function $f : \mathbb{R}^2 \to \mathbb{R}$ which has no pointwise representation
of the form
$$f(x, y) = \sum_{n=1}^{\infty} g_n(x) h_n(y) \qquad (x, y \in \mathbb{R})?$$

Conventions:
- Series convergence is interpreted as pointwise convergence of the ordered partial sums
  $\sum_{n=0}^{N-1} g_n(x) h_n(y) \to f(x, y)$ as $N \to \infty$.
-/

namespace OMA.S_mse_3040258

open Filter Topology

theorem main :
    ∃ f : ℝ → ℝ → ℝ,
      ¬ ∃ (g h : ℕ → ℝ → ℝ),
        ∀ x y : ℝ,
          Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, g n x * h n y) atTop (nhds (f x y)) := by
  sorry

end OMA.S_mse_3040258
