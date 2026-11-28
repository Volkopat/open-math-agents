import Mathlib

namespace OMA.S_mo_114688

universe u

/-- Amenability of an abstract group via a left-invariant finitely additive probability. -/
def Amenable (G : Type u) [Group G] : Prop :=
  ∃ μ : Set G → ℝ,
    (∀ A, 0 ≤ μ A) ∧
      μ Set.univ = 1 ∧
      (∀ A B, Disjoint A B → μ (A ∪ B) = μ A + μ B) ∧
      (∀ (g : G) (A : Set G), μ ((fun a => g * a) '' A) = μ A)

/-- Every infinite amenable group admits a nondiscrete Hausdorff group topology. -/
theorem main :
    ∀ (G : Type u) [Group G], Infinite G → Amenable G →
      ∃ t : TopologicalSpace G,
        @T2Space G t ∧ @IsTopologicalGroup G t _ ∧ ¬ @IsOpen G t ({1} : Set G) := by
  sorry

end OMA.S_mo_114688
