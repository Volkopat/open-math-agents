import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Lander's conjecture

Source: https://en.wikipedia.org/wiki/Difference_set#Ryser_and_Lander_conjectures
Credit: @SubhanAfz
-/

namespace OMA.S_wp_lander_s_conjecture

/-- Each nonidentity element occurs as the difference of exactly `multiplicity` ordered pairs. -/
def IsDifferenceSet {G : Type*} [Group G] [DecidableEq G] (D : Finset G)
    (multiplicity : ℕ) : Prop :=
  ∀ g : G, g ≠ 1 →
    ((D.product D).filter fun x ↦ x.1 * x.2⁻¹ = g).card = multiplicity

/-- The order `D.card - multiplicity` is positive, excluding the zero-order cases
of the empty and full difference sets. -/
theorem main :
    ∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
      (D : Finset G) (multiplicity p : ℕ),
      IsDifferenceSet D multiplicity → multiplicity < D.card → p.Prime →
      p ∣ Fintype.card G → p ∣ D.card - multiplicity →
      ∀ P : Sylow p G, ¬ IsCyclic (P : Subgroup G) := by
  sorry

end OMA.S_wp_lander_s_conjecture
