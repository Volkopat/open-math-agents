import Mathlib

/-!
# MathOverflow 315869

Source: https://mathoverflow.net/questions/315869
-/

namespace OMA.S_mo_315869

open scoped TensorProduct

theorem main : ∀ (R M N : Type) [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N], ∀ f : M →ₗ[R] N, Function.Injective f →
    Function.Injective (TensorProduct.map f (LinearMap.id : N →ₗ[R] N)) := by
  sorry

end OMA.S_mo_315869
