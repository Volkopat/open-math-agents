import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic

/-! Source: https://mathoverflow.net/questions/510148 -/

namespace OMA.S_mo_510148

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Spectral bounds for the normalized covariance matrix, expressed as quadratic-form bounds. -/
def CovarianceBracket {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (n : ℕ) (c₁ C₁ : ℝ) (Y : Option (Fin k) → Ω → ℝ) : Prop :=
  ∀ u : Option (Fin k) → ℝ,
    let q := variance (fun ω => ∑ j, u j * Y j ω) μ / (n : ℝ)
    c₁ * (∑ j, u j ^ 2) ≤ q ∧ q ≤ C₁ * (∑ j, u j ^ 2)

theorem main :
    ∀ (k : ℕ) (c₀ c₁ C₁ : ℝ), 0 < c₀ → 0 < c₁ → c₁ ≤ C₁ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Fin n → Ω → ℝ) (a : Option (Fin k) → Fin n → ℝ),
        iIndepFun X μ →
        (∀ i : Fin n, Measurable (X i) ∧
          (∫ ω, X i ω ∂μ) = 0 ∧ (∀ᵐ ω ∂μ, |X i ω| ≤ 1) ∧
          c₀ ≤ variance (X i) μ) →
        let Y : Option (Fin k) → Ω → ℝ := fun j ω => ∑ i, a j i * X i ω
        let L := Y none
        let P : Ω → Fin k → ℝ := fun ω j => Y (some j) ω
        CovarianceBracket μ n c₁ C₁ Y →
        (∀ j : Fin k, covariance L (fun ω => P ω j) μ = 0) →
        ∀ f : (Fin k → ℝ) → ℝ, Measurable f →
          (∃ M : ℝ, ∀ z, |f z| ≤ M) →
          let F : Ω → ℝ := f ∘ P
          (∫ ω, F ω ∂μ) = 0 →
          ∀ d : ℕ, (d = 1 ∨ d = 2) →
            let Z : Ω → ℝ := fun ω => (L ω) ^ d
            |covariance Z F μ| ≤ C * Real.sqrt (variance Z μ) *
              Real.sqrt (∫ ω, (F ω) ^ 2 ∂μ) / Real.sqrt (n : ℝ) := by
  sorry

end OMA.S_mo_510148
