import Mathlib

/-!
# Is the fixed point property for posets preserved by products?

Source: https://mathoverflow.net/questions/179790/is-the-fixed-point-property-for-posets-preserved-by-products
Credit: @shc261392

A poset `P` has the fixed point property (FPP) if every order-preserving map `f : P → P` has a
fixed point. If `P` and `Q` have the FPP and at least one of them is finite, then `P × Q` (with
the componentwise order) has the FPP (Roddy, 1994).

Question. Suppose `P` and `Q` are two infinite posets with the FPP. Does `P × Q` have the FPP?

Reading used here (the affirmative answer): stated for all posets, which is equivalent since the
case where one factor is finite is Roddy's theorem.
-/

namespace OMA.S_mo_179790

/-- `P` has the fixed point property. -/
def FPP (P : Type*) [Preorder P] : Prop :=
  ∀ f : P →o P, ∃ x, f x = x

theorem main :
    ∀ (P Q : Type) [PartialOrder P] [PartialOrder Q], FPP P → FPP Q → FPP (P × Q) := by
  sorry

end OMA.S_mo_179790
