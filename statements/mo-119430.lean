import Mathlib

/-! Source: https://mathoverflow.net/questions/119430 -/

namespace OMA.S_mo_119430

/-- A common block decomposition into summands invariant under both maps. -/
def HasCommonBlocks {n : ℕ} (A B : Module.End ℂ (Fin n → ℂ)) (k : ℕ) : Prop :=
  ∃ (m : ℕ) (V : Fin m → Submodule ℂ (Fin n → ℂ)),
    DirectSum.IsInternal V ∧
    ∀ i, Module.finrank ℂ (V i) ≤ k ∧
      (∀ v ∈ V i, A v ∈ V i) ∧ (∀ v ∈ V i, B v ∈ V i)

/-- The proposed dimension-independent bound on simultaneous block sizes
for pairs satisfying the cubic relation. -/
theorem main : ∃ k : ℕ, ∀ (n : ℕ) (A B : Module.End ℂ (Fin n → ℂ)),
    A ^ 3 = A → B ^ 3 = B → HasCommonBlocks A B k := by
  sorry

end OMA.S_mo_119430
