import Mathlib

/-!
# A Ramanujan Machine continued fraction for Apéry's constant

Source: https://math.stackexchange.com/questions/4110221
Conjectured by the Ramanujan Machine:
`8/(7 ζ(3)) = 1 - u₁/(v₁ - u₂/(v₂ - u₃/(v₃ - ⋯)))` with `uₙ = n⁶` and
`vₙ = (2n+1)(3n² + 3n + 1)`.

Conventions. The value of the continued fraction is the limit of its truncations
`cf N = 1 - u₁/(v₁ - u₂/(⋯ - u_N/v_N))`, computed by `tail k d` (the tail starting at `v_k`
with `d` further levels).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_4110221

open Filter Topology

/-- `uₙ = n⁶`. -/
def u (n : ℕ) : ℝ := (n : ℝ) ^ 6

/-- `vₙ = (2n+1)(3n² + 3n + 1)`. -/
def v (n : ℕ) : ℝ := (2 * n + 1) * (3 * (n : ℝ) ^ 2 + 3 * n + 1)

/-- `tail k d = v_k - u_{k+1}/(v_{k+1} - ⋯ - u_{k+d}/v_{k+d})`. -/
noncomputable def tail : ℕ → ℕ → ℝ
  | k, 0 => v k
  | k, d + 1 => v k - u (k + 1) / tail (k + 1) d

/-- The truncation of depth `N`. -/
noncomputable def cf (N : ℕ) : ℝ := 1 - u 1 / tail 1 N

theorem main : Tendsto cf atTop (𝓝 (8 / (7 * (riemannZeta 3).re))) := by
  sorry

end OMA.S_mse_4110221
