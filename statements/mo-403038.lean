import Mathlib.Data.Real.Basic

/-!
# Ten real roots in a constrained degree-ten family

Peter Giblin, MathOverflow 403038, 2 September 2021.
Source: https://mathoverflow.net/questions/403038
Credit: @Spinausore

The inner polynomial has no degree-one or degree-seven term. The
injection lists ten distinct real roots and its image is the full zero set.
-/

namespace OMA.S_mo_403038

noncomputable def family (a b c d e f g x : ℝ) : ℝ :=
  x^2 + (x^2 + 1) * (a*x^8 + b*x^6 + c*x^5 + d*x^4 + e*x^3 + f*x^2 + g)

theorem main : ∃ a b c d e f g : ℝ, a < 0 ∧ 0 < g ∧
    ∃ r : Fin 10 → ℝ, Function.Injective r ∧
      ∀ x : ℝ, family a b c d e f g x = 0 ↔ ∃ j, r j = x := by
  sorry

end OMA.S_mo_403038
