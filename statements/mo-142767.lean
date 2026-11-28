import Mathlib

/-!
# MathOverflow 142767

Source: https://mathoverflow.net/questions/142767
-/

namespace OMA.S_mo_142767

open MeasureTheory Filter Set
open scoped Topology ENNReal

def IntegralsConverge {N : ℕ} (μ : ℕ → Measure (Fin N → ℝ))
    (ν : Measure (Fin N → ℝ)) : Prop :=
  ∀ f : (Fin N → ℝ) → ℝ, UniformContinuous f →
    Tendsto (fun n => ∫ x, f x ∂(μ n)) atTop (𝓝 (∫ x, f x ∂ν))

def SetwiseConverges {N : ℕ} (μ : ℕ → Measure (Fin N → ℝ))
    (ν : Measure (Fin N → ℝ)) : Prop :=
  ∀ s : Set (Fin N → ℝ), MeasurableSet s →
    Tendsto (fun n => μ n s) atTop (𝓝 (ν s))

theorem main : ∀ (N : ℕ) (μ : ℕ → Measure (Fin N → ℝ))
    (ν : Measure (Fin N → ℝ)), IntegralsConverge μ ν → SetwiseConverges μ ν := by
  sorry

end OMA.S_mo_142767
