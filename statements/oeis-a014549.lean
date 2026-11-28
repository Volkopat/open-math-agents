import Mathlib

/-!
# OEIS A014549: Gauss's constant as a theta series

Source: https://oeis.org/A014549
Gauss's constant `G = 1 / M(1, √2)`, with `M` the arithmetic-geometric mean. Conjecture:
`G = ∑_{k ≥ 0} A104794(k) / exp(k π)`, where `A104794` is the expansion of `θ₄(q)²`.

Conventions. `θ₄(q) = ∑_{m ∈ ℤ} (-1)^m q^(m²)`, so `A104794 k = ∑ (-1)^(m₁+m₂)` over the integer
pairs with `m₁² + m₂² = k`. `M(1, √2)` is the common limit of `x 0 = 1`, `y 0 = √2`,
`x (k+1) = (x k + y k)/2`, `y (k+1) = √(x k * y k)`; `main` says that `x k` tends to the
reciprocal of the series.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a014549

open Filter Topology Real

/-- The coefficients of `θ₄(q)²` (A104794). -/
noncomputable def A104794 (k : ℕ) : ℤ :=
  ∑ m ∈ (Finset.Icc (-(k : ℤ)) k ×ˢ Finset.Icc (-(k : ℤ)) k).filter
      (fun m => m.1 ^ 2 + m.2 ^ 2 = (k : ℤ)), (-1) ^ (m.1 + m.2).natAbs

/-- The AGM iteration started at `(1, √2)`. -/
noncomputable def agmSeq : ℕ → ℝ × ℝ
  | 0 => (1, √2)
  | k + 1 => (((agmSeq k).1 + (agmSeq k).2) / 2, √((agmSeq k).1 * (agmSeq k).2))

theorem main :
    Tendsto (fun k => (agmSeq k).1) atTop
      (𝓝 (1 / ∑' k : ℕ, (A104794 k : ℝ) / exp (k * π))) := by
  sorry

end OMA.S_oeis_a014549
