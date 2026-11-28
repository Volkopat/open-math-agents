import Mathlib

namespace OMA.S_mo_512896

/-- Can compact subsets be closed under binary intersections but fail to be
closed under countable intersections in a topological space? -/
theorem main :
    ∃ (X : Type) (topology : TopologicalSpace X),
      letI : TopologicalSpace X := topology
      (∀ A B : Set X, IsCompact A → IsCompact B → IsCompact (A ∩ B)) ∧
        ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ¬ IsCompact (⋂ n, K n) := by
  sorry

end OMA.S_mo_512896
