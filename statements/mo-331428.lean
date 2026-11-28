import Mathlib

/-!
# Reduction of a real quartic by a fractional-linear substitution

Source: Paul Ivanov, https://mathoverflow.net/questions/331428 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)

The two monic quadratic factors are specified by their real coefficients.
A fractional-linear change of variables is invertible precisely when
its determinant is nonzero. The rational-function identity is required
at every real parameter where its denominator is nonzero.
-/

namespace OMA.S_mo_331428

def ReducibleQuartic (a p₁ q₁ p₂ q₂ : ℝ) : Prop :=
  ∃ α β γ M₁ N₁ M₂ N₂ : ℝ, α-β*γ ≠ 0 ∧
    ∀ t : ℝ, γ*t+1 ≠ 0 →
      let x := (α*t+β)/(γ*t+1)
      a*(x^2+p₁*x+q₁)*(x^2+p₂*x+q₂) =
        ((M₁+N₁*t^2)*(M₂+N₂*t^2))/(γ*t+1)^4

theorem main : ∀ (a p₁ q₁ p₂ q₂ : ℝ), a ≠ 0 → ReducibleQuartic a p₁ q₁ p₂ q₂ := by
  sorry

end OMA.S_mo_331428
