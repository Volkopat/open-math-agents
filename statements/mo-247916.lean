import Mathlib

/-!
# A relation between intersection and product on Boolean interval of finite groups

Source: https://mathoverflow.net/questions/247916
Credit: @datdzrgb

The interval from H to G is the upper interval of H in the subgroup lattice.
A finite Boolean lattice is order-isomorphic to the powerset of a finite set.
-/

namespace OMA.S_mo_247916

open scoped Pointwise

def subgroupSet {G : Type*} [Group G] {H : Subgroup G} (K : Set.Ici H) : Set G :=
  (K.val : Set G)

theorem main :
    ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G),
      (∃ r : ℕ, Nonempty (Set.Ici H ≃o Set (Fin r))) →
      ∀ (A B Acomp Bcomp ABcomp : Set.Ici H),
        IsCompl A Acomp → IsCompl B Bcomp → IsCompl (A ⊓ B) ABcomp →
        (subgroupSet A * subgroupSet Acomp) ∩ (subgroupSet B * subgroupSet Bcomp) ⊆
          subgroupSet (A ⊓ B) * subgroupSet ABcomp := by
  sorry

end OMA.S_mo_247916
