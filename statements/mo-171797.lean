import Mathlib

namespace OMA.S_mo_171797

/-- Is there an infinite field of characteristic two whose multiplicative
group is torsion free and has no direct sum decomposition with two nontrivial factors? -/
theorem main :
    ∃ (F : Type) (field : Field F),
      letI := field
      Infinite F ∧ CharP F 2 ∧
        (∀ (u : Fˣ) (n : ℕ), 0 < n → u ^ n = 1 → u = 1) ∧
        (∀ H K : Subgroup Fˣ, IsCompl H K → H = ⊥ ∨ K = ⊥) := by
  sorry

end OMA.S_mo_171797
