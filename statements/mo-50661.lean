import Mathlib

/-!
# Unboundedness of the number of integral points on elliptic curves

Source: https://mathoverflow.net/questions/50661
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (MathOverflow): put an elliptic curve `E/ℚ` into minimal Weierstrass form and let `n(E)`
be its number of integral points. Is `n(E)` unbounded as `E` ranges over all elliptic curves?

Conventions:
* A Weierstrass curve over `ℚ` is integral if all of `a₁, a₂, a₃, a₄, a₆` are integers; it is a
  (global) minimal model if it is integral and no integral curve obtained from it by a change of
  variables over `ℚ` (Mathlib's `VariableChange ℚ` action) has smaller `|Δ|`. Elliptic means
  `Δ ≠ 0`.
* Integral points are `(x, y) ∈ ℤ²` on the affine Weierstrass equation (the point at infinity is
  not counted; this does not affect unboundedness).
* The source asks a yes/no question; `main` states the answer yes (unbounded), and a disproof
  would answer no.
-/

namespace OMA.S_mo_50661

/-- All Weierstrass coefficients are integers. -/
def IsIntegralModel (W : WeierstrassCurve ℚ) : Prop :=
  ∀ c ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set ℚ), ∃ z : ℤ, (z : ℚ) = c

/-- A global minimal model over `ℤ`. -/
def IsGlobalMinimal (W : WeierstrassCurve ℚ) : Prop :=
  IsIntegralModel W ∧ W.Δ ≠ 0 ∧
    ∀ C : WeierstrassCurve.VariableChange ℚ, IsIntegralModel (C • W) → |W.Δ| ≤ |(C • W).Δ|

/-- The integral points of the affine Weierstrass equation. -/
def integralPoints (W : WeierstrassCurve ℚ) : Set (ℤ × ℤ) :=
  {p | (p.2 : ℚ) ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2 =
    (p.1 : ℚ) ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆}

theorem main :
    ∀ N : ℕ, ∃ W : WeierstrassCurve ℚ, IsGlobalMinimal W ∧
      N ≤ (integralPoints W).ncard ∧ (integralPoints W).Finite := by
  sorry

end OMA.S_mo_50661
