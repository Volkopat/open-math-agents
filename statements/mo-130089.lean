import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.NumberField.Discriminant.Defs

namespace OMA.S_mo_130089

/-- The number of unital subrings of a given additive index. -/
noncomputable def subringCount (R : Type*) [Ring R] (index : ℕ) : ℕ∞ :=
  {S : Subring R | S.toAddSubgroup.index = index}.encard

/-- At an unramified prime, the number of orders of any given
prime-power index is bounded by the split integral model. -/
theorem main :
    ∀ (K : Type*) [Field K] [NumberField K] (p r : ℕ),
      p.Prime → ¬ ((p : ℤ) ∣ NumberField.discr K) →
        subringCount (NumberField.RingOfIntegers K) (p ^ r) ≤
          subringCount (Fin (Module.finrank ℚ K) → ℤ) (p ^ r) := by
  sorry

end OMA.S_mo_130089
