import Mathlib

/-!
# A strictly increasing rational function with derivative zero

Source: https://math.stackexchange.com/questions/1911440
Credit: @zarnab222-dev

Both the argument and value of the function are rational. Differentiability
uses the usual absolute value on the rationals.
-/

namespace OMA.S_mse_1911440

theorem main : ∃ f : ℚ → ℚ, StrictMono f ∧ ∀ q : ℚ, HasDerivAt f 0 q := by
  sorry

end OMA.S_mse_1911440
