import Mathlib

/-!
# MathOverflow 186002

Source: https://mathoverflow.net/questions/186002
-/

namespace OMA.S_mo_186002



theorem main : ∀ (R : Type) [CommRing R], (∀ a : R, ∃ x : R, a * x * a = a) →
      ∀ a : R, ¬ IsUnit a → ∃ b : R, b ≠ 0 ∧ a * b = 0 := by
  sorry

end OMA.S_mo_186002
