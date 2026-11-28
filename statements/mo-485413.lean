import Mathlib

/-!
# Trace and Frobenius norm of products of random hyperplane projections

Source: Yaroslav Bulatov, https://mathoverflow.net/questions/485413 (CC BY-SA 4.0).
Credit: @connoranderson. Nathaniel Johnston pointed out the deterministic lower
inequality in the original discussion. The suggested upper inequality fails on
an open set of positive probability for every d≥3 and every odd power, however
large. At power one the two quantities have exactly the same expectation.

The sphere carries its Euclidean topology. We state positive probability for
every full-support probability law and the mean formulas for all isotropic
sphere laws. The rotation-invariant uniform probability law has both properties.
The k-fold product measure samples independent directions.
-/

namespace OMA.S_mo_485413
open Matrix Finset MeasureTheory
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Sphere (d : ℕ) := Metric.sphere (0:E d) 1
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

noncomputable def proj {d : ℕ} (v : Sphere d) : Mat d :=
  1 - vecMulVec (fun i => v.val i) (fun i => v.val i)
noncomputable def walk {d k : ℕ} (w : Fin k → Sphere d) : Mat d :=
  (List.ofFn (fun i => proj (w i))).prod
def froSq {d : ℕ} (M : Mat d) : ℝ := ∑ i,∑ j,(M i j)^2

def iso {d : ℕ} (μ : Measure (Sphere d)) : Prop := ∀ i j : Fin d,
  (∫ v : Sphere d, v.val i * v.val j ∂μ) = if i=j then 1/(d:ℝ) else 0

noncomputable def sphereAction {d : ℕ} (U : E d ≃ₗᵢ[ℝ] E d) (v : Sphere d) : Sphere d :=
  ⟨U v.val, by simp⟩
def orthInvariant {d : ℕ} (μ : Measure (Sphere d)) : Prop :=
  ∀ U : E d ≃ₗᵢ[ℝ] E d, MeasurePreserving (sphereAction U) μ μ

theorem main :
    (∀ (d : ℕ) (M : Mat d) (s : ℕ), (M^(2*s)).trace ≤ froSq (M^s)) ∧
    (∀ (d : ℕ), 3≤d → ∀ (s : ℕ), Odd s → ∀ (μ : Measure (Sphere d))
      [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure],
      0 < (Measure.pi (fun _ : Fin d => μ))
        {w : Fin d → Sphere d | ((walk w)^s).trace < froSq ((walk w)^s)}) ∧
    (∀ (d : ℕ), 0<d → ∀ (μ : Measure (Sphere d)) [IsProbabilityMeasure μ], iso μ → ∀ k : ℕ,
      (∫ w : Fin k → Sphere d, (walk w).trace ∂Measure.pi (fun _ => μ)) =
        (d:ℝ)*(1-1/(d:ℝ))^k ∧
      (∫ w : Fin k → Sphere d, froSq (walk w) ∂Measure.pi (fun _ => μ)) =
        (d:ℝ)*(1-1/(d:ℝ))^k) ∧
    (∀ (d : ℕ), 0<d → ∀ (μ : Measure (Sphere d)) [IsProbabilityMeasure μ],
      orthInvariant μ → iso μ) := by
  sorry
end OMA.S_mo_485413
