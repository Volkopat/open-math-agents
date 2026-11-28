import Mathlib

/-!
# Rational ratio of sines at distinct rational multiples of $\pi$

Source: https://math.stackexchange.com/questions/5112273/do-there-exist-alpha-beta-in-0-pi-2-that-are-distinct-rational-multipl
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Do there exist distinct $\alpha, \beta \in (0, \pi / 2)$ that are rational multiples of $\pi$
such that $\frac{\sin \alpha}{\sin \beta} \in \mathbb{Q}$?
-/

namespace OMA.S_mse_5112273

theorem main :
    ∃ (p q : ℚ),
      (0 : ℝ) < (p : ℝ) ∧ (p : ℝ) < 1 / 2 ∧
      (0 : ℝ) < (q : ℝ) ∧ (q : ℝ) < 1 / 2 ∧
      p ≠ q ∧
      ∃ r : ℚ, Real.sin ((p : ℝ) * Real.pi) / Real.sin ((q : ℝ) * Real.pi) = (r : ℝ) := by
  sorry

end OMA.S_mse_5112273
