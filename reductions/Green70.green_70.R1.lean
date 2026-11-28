import FormalConjectures.GreensOpenProblems.«70»

-- Reduction Green70.green_70.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Green70_green_70_R1

def H1 : Prop := ∀ k : ℕ, ∃ n₀ : ℕ, ∀ P : Finset (ℝ × ℝ),
  n₀ ≤ P.card → Green70.HasCollinear k P ∨ Green70.HasMutuallyVisible 5 P

def H2 : Prop := ∀ k ℓ : ℕ, ℓ ≠ 5 → ∃ n₀ : ℕ, ∀ P : Finset (ℝ × ℝ),
  n₀ ≤ P.card → Green70.HasCollinear k P ∨ Green70.HasMutuallyVisible ℓ P

theorem main : H1 → H2 → type_of% @Green70.green_70 := by
  intro h1 h2 k ℓ
  by_cases h : ℓ = 5
  · subst ℓ
    exact h1 k
  · exact h2 k ℓ h

end OMA.R_Green70_green_70_R1
