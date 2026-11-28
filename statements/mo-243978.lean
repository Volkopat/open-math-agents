import Mathlib

/-!
# Differential equation with inequality constraints

Source: https://mathoverflow.net/questions/243978
Asked by MathOverflow user Daishisan.

The question asks: does there exist `γ > 0` and functions `g` and `f` such that for all
`x ∈ [0, 1]`
* `g(x) ∈ [0, 1]`,
* `f(x) ∈ [0, x]`,
* `x * g'(x) - (g f)'(x) = 0`,
* `g(x) f(x) ≥ γ x`?

Translation choices.
* `g` and `f` are real functions; only their values on `[0, 1]` matter.
* The equation involves the derivatives of `g` and of the product `g f` on `[0, 1]`, so
  these two functions are required to be differentiable on `[0, 1]` (one-sided at the
  endpoints): `g'` and `h'` are functions with `HasDerivWithinAt g (g' x) (Icc 0 1) x` and
  `HasDerivWithinAt (g f) (h' x) (Icc 0 1) x` for every `x ∈ [0, 1]`. No differentiability
  of `f` itself is assumed.
* `main` is the affirmative answer: such `γ`, `g`, `f` exist.
-/

namespace OMA.S_mo_243978

open Set

theorem main :
    ∃ γ : ℝ, 0 < γ ∧ ∃ g f g' h' : ℝ → ℝ, ∀ x ∈ Icc (0 : ℝ) 1,
      g x ∈ Icc (0 : ℝ) 1 ∧ f x ∈ Icc 0 x ∧
      HasDerivWithinAt g (g' x) (Icc 0 1) x ∧
      HasDerivWithinAt (fun y => g y * f y) (h' x) (Icc 0 1) x ∧
      x * g' x - h' x = 0 ∧ γ * x ≤ g x * f x := by
  sorry

end OMA.S_mo_243978
