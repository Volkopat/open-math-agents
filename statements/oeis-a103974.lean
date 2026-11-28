import Mathlib

/-!
# OEIS A103974: almost-equilateral triangles (a, a, a+1) with integer area

Source: https://oeis.org/A103974
Smaller sides `a` of `(a, a, a+1)` integer triangles with integer area; equivalently, positive
integers `a` such that `3/16 a⁴ + 1/4 a³ - 1/8 a² - 1/4 a - 1/16` (the squared area, by Heron's
formula) is a square. Conjecture: `a(n+1)/a(n) → 7 + 4√3`.

Conventions. "Integer area" means the squared area equals `m²` for a natural number `m`;
`a` is indexed from `0` over positive `a`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a103974

open Filter Topology Real

/-- `(a, a, a+1)` has integer area. -/
def P (a : ℕ) : Prop :=
  1 ≤ a ∧ ∃ m : ℕ, (m : ℚ) ^ 2 =
    3 / 16 * (a : ℚ) ^ 4 + 1 / 4 * (a : ℚ) ^ 3 - 1 / 8 * (a : ℚ) ^ 2 - 1 / 4 * a - 1 / 16

theorem main :
    Tendsto (fun n : ℕ => (Nat.nth P (n + 1) : ℝ) / Nat.nth P n) atTop (𝓝 (7 + 4 * √3)) := by
  sorry

end OMA.S_oeis_a103974
