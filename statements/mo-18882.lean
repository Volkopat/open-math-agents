import Mathlib

namespace OMA.S_mo_18882

/-- The continuous real self-maps having continuous iterative square roots
contain an infinite-dimensional real linear subspace. -/
theorem main :
    ∃ E : Submodule ℝ C(ℝ, ℝ),
      ¬ FiniteDimensional ℝ E ∧
        ∀ g : C(ℝ, ℝ), g ∈ E → ∃ f : C(ℝ, ℝ), f.comp f = g := by
  sorry

end OMA.S_mo_18882
