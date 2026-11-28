import Mathlib

/-!
# The Krzyż conjecture

Source: https://mathoverflow.net/questions/297054
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Krzyż, 1968): if `f(z) = ∑ a_n zⁿ` is analytic in the unit disk, `0 < |f(z)| ≤ 1`
there, then `|a_n| ≤ 2/e` for all `n ≥ 1`.

Conventions:
* `f` is analytic on the open unit disk (`DifferentiableOn ℂ f (ball 0 1)`), nonvanishing and
  bounded by `1` there; `a_n = f⁽ⁿ⁾(0)/n!` is its `n`-th Taylor coefficient at `0`.
-/

namespace OMA.S_mo_297054

theorem main :
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0 ∧ ‖f z‖ ≤ 1) →
      ∀ n : ℕ, 1 ≤ n → ‖iteratedDeriv n f 0 / n.factorial‖ ≤ 2 / Real.exp 1 := by
  sorry

end OMA.S_mo_297054
