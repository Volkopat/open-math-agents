import Mathlib

namespace OMA.S_mo_172530

/-- Does some finitely generated torsion-free group fail the unique products
property while every unit of its complex group ring has singleton support? -/
theorem main :
    ∃ (G : Type) (group : Group G),
      letI : Group G := group
      Group.FG G ∧
        (∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1) ∧
        ¬ UniqueProds G ∧
        ∀ u : (MonoidAlgebra ℂ G)ˣ,
          ∃ (c : ℂ) (g : G), c ≠ 0 ∧ u.val = MonoidAlgebra.single g c := by
  sorry

end OMA.S_mo_172530
