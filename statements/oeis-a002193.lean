import Mathlib

/-!
# OEIS A002193: √2 as a theta-quotient series

Source: https://oeis.org/A002193
Conjecture on the entry: `√2 = ∑_{k ≥ 0} A014969(k) / exp(k π)`, where `A014969` is the
expansion of `(θ₃(q)/θ₄(q))²`. (The entry also records a conjectured limit involving
A167199; `main` states the theta-series conjecture.)

Conventions. With `r₃ k = #{(x, y) ∈ ℤ² | x² + y² = k}` and
`r₄ k = ∑_{x² + y² = k} (-1)^(x+y)` (the coefficients of `θ₃²` and `θ₄²`), the coefficients
`b` of `(θ₃/θ₄)²` are determined by `∑_{i ≤ k} b i * r₄ (k - i) = r₃ k`; since `r₄ 0 = 1`
this gives `b k = r₃ k - ∑_{i < k} b i * r₄ (k - i)`, computed by `bList`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a002193

open Real

/-- Integer pairs `(x, y)` with `x² + y² = k`. -/
noncomputable def reps (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(k : ℤ)) k ×ˢ Finset.Icc (-(k : ℤ)) k).filter fun m => m.1 ^ 2 + m.2 ^ 2 = k

/-- Coefficients of `θ₃²`. -/
noncomputable def r₃ (k : ℕ) : ℤ := (reps k).card

/-- Coefficients of `θ₄²`. -/
noncomputable def r₄ (k : ℕ) : ℤ := ∑ m ∈ reps k, (-1) ^ (m.1 + m.2).natAbs

/-- The first `k + 1` coefficients of `(θ₃/θ₄)²`. -/
noncomputable def bList : ℕ → List ℤ
  | 0 => [r₃ 0]
  | k + 1 =>
      bList k ++ [r₃ (k + 1) - ∑ i ∈ Finset.range (k + 1), (bList k).getD i 0 * r₄ (k + 1 - i)]

/-- A014969. -/
noncomputable def b (k : ℕ) : ℤ := (bList k).getD k 0

theorem main : ∑' k : ℕ, (b k : ℝ) / exp (k * π) = √2 := by
  sorry

end OMA.S_oeis_a002193
