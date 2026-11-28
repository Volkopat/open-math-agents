import Mathlib

/-!
# Is `⌊exp(p_{n²}# / p_{n²+1})⌋` always a square?

Source: https://math.stackexchange.com/questions/2645263
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

With `pₙ` the `n`-th prime and `pₙ# = p₁ ⋯ pₙ` the primorial, the asker observed
`⌊e^(p₁#/p₂)⌋ = 1²` and `⌊e^(p₄#/p₅)⌋ = ⌊e^(210/11)⌋ = 13981²`, and conjectured that
`⌊exp(p_{n²}# / p_{n²+1})⌋` is a perfect square for every `n ≥ 1`.

Conventions:
* `pᵢ = Nat.nth Nat.Prime (i - 1)` (`p₁ = 2`); `pₙ# = ∏_{i=1}^{n} pᵢ`.
-/

namespace OMA.S_mse_2645263

/-- The `i`-th prime, `p₁ = 2`. -/
noncomputable def p (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- The primorial `p₁ ⋯ pₙ`. -/
noncomputable def primorial (n : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 n, p i

/-- `⌊exp(p_{n²}#/p_{n²+1})⌋` is a perfect square for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    IsSquare ⌊Real.exp ((primorial (n ^ 2) : ℝ) / p (n ^ 2 + 1))⌋ := by
  sorry

end OMA.S_mse_2645263
