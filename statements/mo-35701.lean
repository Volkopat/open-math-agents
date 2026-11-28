import Mathlib.Algebra.Group.Subgroup.Basic

namespace OMA.S_mo_35701

/-- If a characteristic subgroup has characteristic direct square,
then every finite direct power of it is characteristic. -/
theorem main :
    ∀ (G : Type*) [Group G] (H : Subgroup G),
      H.Characteristic → (H.prod H).Characteristic →
        ∀ n : ℕ,
          (Subgroup.pi Set.univ (fun _ : Fin n => H)).Characteristic := by
  sorry

end OMA.S_mo_35701
