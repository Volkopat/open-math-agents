import Mathlib

/-!
# MathOverflow 275030

Source: https://mathoverflow.net/questions/275030
-/

namespace OMA.S_mo_275030

open Function Set

/-- Finite principal neighborhoods give one precise local finiteness condition. -/
def FinitePrincipalNeighborhoods (P : Type) [PartialOrder P] : Prop :=
  ∀ x : P, (Iic x).Finite ∧ (Ici x).Finite

theorem main : (∀ (P : Type) [PartialOrder P], Nonempty (P ↪o (P → ℝ))) ∧
    (∀ (P : Type) [PartialOrder P] [Countable P], ∃ f : P → ℝ, Injective f ∧ Monotone f) ∧
    (∃ (P : Type) (order : PartialOrder P), letI := order
      Countable P ∧ FinitePrincipalNeighborhoods P ∧
        ∀ d : ℕ, IsEmpty (P ↪o (Fin d → ℝ))) ∧
    (∃ (P : Type) (order : PartialOrder P), letI := order
      FinitePrincipalNeighborhoods P ∧
        ∀ d : ℕ, ¬ ∃ f : P → Fin d → ℝ, Injective f ∧ Monotone f) := by
  sorry

end OMA.S_mo_275030
