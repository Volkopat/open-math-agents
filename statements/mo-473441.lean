import Mathlib.Data.Set.Function
import Mathlib.Data.Nat.Basic

/-! Source: https://mathoverflow.net/questions/473441 -/

namespace OMA.S_mo_473441

def Dodges (S : Set (Set ℕ)) : Prop :=
  ∃ σ : Equiv.Perm ℕ, ∀ t ∈ S, σ '' t ∉ S

theorem main :
    ∀ S : Set (Set ℕ), Dodges S →
      ∃ T : Set (Set ℕ), S ⊆ T ∧ Dodges T ∧
        ∀ t : Set ℕ, t ∉ T → ¬ Dodges (insert t T) := by
  sorry

end OMA.S_mo_473441
