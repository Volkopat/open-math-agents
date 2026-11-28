import Mathlib

/-!
# Kernels of derivations and hyperreflexivity

Source: E. Papapetros, https://mathoverflow.net/questions/478297 (CC BY-SA).
Lean formalization: @my-other-github-account.
-/
namespace OMA.S_mo_478297

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Hyperreflexivity using the annihilating unit-vector pairs in the question. -/
def Hyperreflexive (S : Set (H →L[ℂ] H)) : Prop :=
  ∃ k : ℝ, 0 < k ∧ ∀ T : H →L[ℂ] H,
    sInf ((fun X => ‖T - X‖) '' S) ≤ k * sSup {r : ℝ | ∃ ξ η : H,
      ‖ξ‖ = 1 ∧ ‖η‖ = 1 ∧ (∀ X ∈ S, ⟪X ξ, η⟫_ℂ = 0) ∧ r = ‖⟪T ξ, η⟫_ℂ‖}

/-- Use the bicommutant characterization of a concrete von Neumann algebra.
The projection acts on H and need not belong to A. -/
theorem main : ∀ (A : StarSubalgebra ℂ (H →L[ℂ] H)),
    Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) = A →
    Hyperreflexive (A : Set (H →L[ℂ] H)) →
    ∀ P : H →L[ℂ] H, IsStarProjection P →
    Hyperreflexive {X : H →L[ℂ] H | X ∈ A ∧ X * P - P * X = 0} := by
  sorry

end OMA.S_mo_478297
