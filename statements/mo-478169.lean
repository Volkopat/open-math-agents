import Mathlib

namespace OMA.S_mo_478169

/-- Does every map of associative unital rings preserving multiplication
and successor preserve addition? -/
theorem main :
    ∀ (R S : Type) [Ring R] [Ring S] (f : R → S),
      (∀ x y : R, f (x * y) = f x * f y) →
      (∀ x : R, f (1 + x) = 1 + f x) →
        ∀ x y : R, f (x + y) = f x + f y := by
  sorry

end OMA.S_mo_478169
