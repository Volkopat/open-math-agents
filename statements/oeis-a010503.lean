import Mathlib

/-!
# OEIS A010503: 1/√2 as a theta-quotient series

Source: https://oeis.org/A010503
Conjecture on the entry: `1/√2 = ∑_{k ≥ 0} A139820(k) / exp(k π)`, where `A139820` is the
expansion of `(φ(-q)/φ(q))² = (θ₄(q)/θ₃(q))²`.

Conventions. With `r₃ k = #{(x, y) ∈ ℤ² | x² + y² = k}` and
`r₄ k = ∑_{x² + y² = k} (-1)^(x+y)` (the coefficients of `θ₃²` and `θ₄²`), the coefficients
`c` of `(θ₄/θ₃)²` are determined by `∑_{i ≤ k} c i * r₃ (k - i) = r₄ k`; since `r₃ 0 = 1`
this gives `c k = r₄ k - ∑_{i < k} c i * r₃ (k - i)`, computed by `cList`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a010503

open Real

/-- Integer pairs `(x, y)` with `x² + y² = k`. -/
noncomputable def reps (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(k : ℤ)) k ×ˢ Finset.Icc (-(k : ℤ)) k).filter fun m => m.1 ^ 2 + m.2 ^ 2 = k

/-- Coefficients of `θ₃²`. -/
noncomputable def r₃ (k : ℕ) : ℤ := (reps k).card

/-- Coefficients of `θ₄²`. -/
noncomputable def r₄ (k : ℕ) : ℤ := ∑ m ∈ reps k, (-1) ^ (m.1 + m.2).natAbs

/-- The first `k + 1` coefficients of `(θ₄/θ₃)²`. -/
noncomputable def cList : ℕ → List ℤ
  | 0 => [r₄ 0]
  | k + 1 =>
      cList k ++ [r₄ (k + 1) - ∑ i ∈ Finset.range (k + 1), (cList k).getD i 0 * r₃ (k + 1 - i)]

/-- A139820. -/
noncomputable def c (k : ℕ) : ℤ := (cList k).getD k 0

theorem main : ∑' k : ℕ, (c k : ℝ) / exp (k * π) = 1 / √2 := by
  sorry

end OMA.S_oeis_a010503
