import Mathlib

/-!
# Frankl's conjecture for infinite families

Source: https://math.stackexchange.com/questions/4107563
Let `A` be a set and `F ⊆ 𝒫(A)` closed under arbitrary intersections and not a finite union of
chains. For `a ∈ A` let `F_a = {X ∈ F | a ∈ X}`. Must there exist `a ∈ A` with
`#F_a ≤ #(F \ F_a)`? `main` states the affirmative answer.

Conventions. Closure under arbitrary intersections includes the empty intersection, so
`A ∈ F`. Cardinalities are Mathlib cardinals (`Cardinal.mk`). A chain is a set of subsets
totally ordered by inclusion (`IsChain (· ⊆ ·)`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_4107563

theorem main :
    ∀ (A : Type) (F : Set (Set A)),
      (∀ E ⊆ F, ⋂₀ E ∈ F) →
      (¬ ∃ (n : ℕ) (C : Fin n → Set (Set A)), (∀ i, IsChain (· ⊆ ·) (C i)) ∧ F = ⋃ i, C i) →
      ∃ a : A, Cardinal.mk {X // X ∈ F ∧ a ∈ X} ≤ Cardinal.mk {X // X ∈ F ∧ a ∉ X} := by
  sorry

end OMA.S_mse_4107563
