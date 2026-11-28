import Mathlib.Data.Finite.Defs
import Mathlib.Order.Hom.Basic

namespace OMA.S_mo_373829

universe u

/-- Every finite partial order has an endomorphism whose centralizer among the
order automorphisms consists of the identity. -/
theorem main :
    ∀ (P : Type u) [PartialOrder P] [Finite P],
      ∃ f : P →o P, ∀ e : P ≃o P,
        Function.Commute (f : P → P) (e : P → P) → e = OrderIso.refl P := by
  sorry

end OMA.S_mo_373829
