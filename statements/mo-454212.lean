import Mathlib

/-!
# MathOverflow 454212

Source: https://mathoverflow.net/questions/454212
-/

namespace OMA.S_mo_454212

open scoped BigOperators

def IsNormalizedNegativeType {G : Type} [Group G] (d : G → ℝ) : Prop :=
  (∀ g, 0 ≤ d g) ∧ d 1 = 0 ∧ (∀ g, d g⁻¹ = d g) ∧
    ∀ (n : ℕ) (g : Fin n → G) (c : Fin n → ℝ), (∑ i, c i) = 0 →
      ∑ i, ∑ j, c i*c j*d ((g i)⁻¹*g j) ≤ 0

theorem main : ∀ (G : Type) [Group G] (d : G → ℝ), IsNormalizedNegativeType d →
      ∀ g h : G, Real.sqrt (d (g*h)) ≤ Real.sqrt (d g)+Real.sqrt (d h) := by
  sorry

end OMA.S_mo_454212
