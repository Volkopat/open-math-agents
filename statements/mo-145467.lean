import Mathlib

/-!
# A challenging non-homogeneous fractional inequality

Source: https://mathoverflow.net/questions/145467
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (MathOverflow, prove or disprove): let `n ∈ ℕ`, `λ > 1`, `k = λn` and
`c = (λ - 1/n)/(λ - 1) = (k - 1)/(k - n)`. For reals `a₁, …, a_n ≥ 0` put `r = ∏ a_i^c`. Then
`∑ (1 - a_i)/(1 - a_i^{λn}) ≥ (1 - r)/(1 - r^λ)`.

Conventions:
* `n ≥ 1`. The quotient `(1 - t)/(1 - t^s)` (`s > 0`, `t ≥ 0`) is extended continuously by its
  limit `1/s` at `t = 1`. Real powers are `Real.rpow`.
* `main` states the inequality (the "prove" alternative); a counterexample would disprove it.
-/

namespace OMA.S_mo_145467

/-- `(1 - t)/(1 - t^s)`, with the value `1/s` at `t = 1`. -/
noncomputable def q (t s : ℝ) : ℝ := if t = 1 then 1 / s else (1 - t) / (1 - t ^ s)

theorem main :
    ∀ (n : ℕ) (lam : ℝ) (a : Fin n → ℝ), 1 ≤ n → 1 < lam → (∀ i, 0 ≤ a i) →
      let c := (lam - 1 / n) / (lam - 1)
      let r := ∏ i, a i ^ c
      q r lam ≤ ∑ i, q (a i) (lam * n) := by
  sorry

end OMA.S_mo_145467
