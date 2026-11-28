import Mathlib

/-!
# A060294: Decimal expansion of Buffon's constant 2/Pi

Source: https://oeis.org/A060294
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
For every nonzero integer `m`,
`lim_{n → ∞} (1 / n) * ∑_{k = 1}^n |sin(k * m)| = 2 / π`,
and likewise
`lim_{n → ∞} (1 / n) * ∑_{k = 1}^n |cos(k * m)| = 2 / π`.
-/

namespace OMA.S_oeis_a060294

/-- For every nonzero integer `m`, the Cesàro means of `|sin(k * m)|` and `|cos(k * m)|`
both converge to `2 / π`. -/
theorem main :
    ∀ m : ℤ, m ≠ 0 →
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, |Real.sin ((k : ℝ) * (m : ℝ))|)
        Filter.atTop (nhds (2 / Real.pi)) ∧
      Filter.Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, |Real.cos ((k : ℝ) * (m : ℝ))|)
        Filter.atTop (nhds (2 / Real.pi)) := by
  sorry

end OMA.S_oeis_a060294
