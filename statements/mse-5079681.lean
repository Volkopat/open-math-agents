import Mathlib

/-!
# Leading digit of the prime zeta function versus `5ⁿ`

Source: https://math.stackexchange.com/questions/5079681
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture 1 (asker): for all integers `n ≥ 10`, the leading decimal digit of the prime zeta
value `P(n) = ∑_p p^(-n)` equals the leading digit of `5ⁿ`.

Conventions:
* `P(n)` is the `tsum` over primes of `p^(-n)` (equal to the source's `∑ μ(k) log ζ(nk)/k`).
  The leading digit of `x > 0` is `⌊x / 10^⌊log₁₀ x⌋⌋`.
-/

namespace OMA.S_mse_5079681

/-- The prime zeta function at an integer `n ≥ 2`. -/
noncomputable def P (n : ℕ) : ℝ := ∑' p : {p : ℕ // p.Prime}, ((p : ℕ) : ℝ)⁻¹ ^ n

/-- Leading decimal digit of `x > 0`. -/
noncomputable def ld (x : ℝ) : ℤ := ⌊x / 10 ^ ⌊Real.logb 10 x⌋⌋

/-- For `n ≥ 10`, `ld(P(n)) = ld(5ⁿ)`. -/
theorem main : ∀ n : ℕ, 10 ≤ n → ld (P n) = ld ((5 : ℝ) ^ n) := by
  sorry

end OMA.S_mse_5079681
