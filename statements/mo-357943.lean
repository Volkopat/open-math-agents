import Mathlib

/-!
# Angular second moments of subgaussian random vectors

Source: dohmatob, https://mathoverflow.net/questions/357943 (CC BY-SA 4.0).
Credit: @connoranderson. The question's body assumes subgaussian linear
projections. Its title also mentions a uniform direction. These hypotheses
give different estimates, so the last assertion includes the orthogonally
invariant case discussed in the author's comment.

At zero the normalized vector is defined to be zero. All positive semidefinite
matrices with trace at most one occur, even for centered finitely supported
laws with any prescribed positive subgaussian parameter.
-/
namespace OMA.S_mo_357943
open Matrix Finset MeasureTheory ProbabilityTheory
open scoped NNReal
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev Sphere (d : ℕ) := Metric.sphere (0 : E d) 1

noncomputable def direction {d : ℕ} (x : E d) : E d := ‖x‖⁻¹ • x
noncomputable def angular {d : ℕ} (μ : Measure (E d)) : Mat d :=
  fun i j => ∫ x, direction x i * direction x j ∂μ
def subgaussian {d : ℕ} (μ : Measure (E d)) (σ : ℝ≥0) : Prop :=
  ∀ v : E d, ‖v‖=1 → HasSubgaussianMGF (fun x => inner ℝ v x) (σ^2) μ
noncomputable def sphereAction {d : ℕ} (U : E d ≃ₗᵢ[ℝ] E d) (v : Sphere d) :
    Sphere d := ⟨U v.val, by simp⟩
def orthInvariant {d : ℕ} (ν : Measure (Sphere d)) : Prop :=
  ∀ U : E d ≃ₗᵢ[ℝ] E d, MeasurePreserving (sphereAction U) ν ν

theorem main :
    (∀ (d : ℕ) (μ : Measure (E d)) [IsProbabilityMeasure μ],
      (angular μ).PosSemidef ∧ (angular μ).trace ≤ 1) ∧
    (∀ (d : ℕ) (M : Mat d), M.PosSemidef → M.trace ≤ 1 →
      ∀ σ : ℝ≥0, 0 < σ → ∃ μ : Measure (E d), IsProbabilityMeasure μ ∧
        subgaussian μ σ ∧ angular μ = M ∧
        ∃ S : Finset (E d), S.card ≤ 2*d+1 ∧ μ (S : Set (E d))ᶜ = 0) ∧
    (∀ (d : ℕ), 0<d → ∀ (ν : Measure (Sphere d)) [IsProbabilityMeasure ν],
      orthInvariant ν → ∀ i j : Fin d, (∫ v : Sphere d, v.val i * v.val j ∂ν) =
        if i=j then 1/(d:ℝ) else 0) := by
  sorry
end OMA.S_mo_357943
