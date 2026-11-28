import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
MathOverflow 245620, PThomasCS (2016):
https://mathoverflow.net/questions/245620/is-this-extension-of-hoeffdings-inequality-known

This states the literal displayed strict inequality, including constant random variables.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace OMA.S_mo_245620

/-- The largest of a nonempty collection of real observations. -/
noncomputable def sampleMax {Ω : Type} {n : ℕ}
    (X : Fin (n + 1) → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)

/-- The literal strict confidence assertion in MathOverflow question 245620.
The sample size is `n + 1`, so every positive sample size is represented. -/
def ClaimedBound : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (X : Fin (n + 1) → Ω → ℝ) (a b δ : ℝ),
    (∀ i, Measurable (X i)) →
    iIndepFun X μ →
    (∀ i, IdentDistrib (X i) (X 0) μ μ) →
    (∀ i, ∀ᵐ ω ∂μ, a ≤ X i ω ∧ X i ω ≤ b) →
    0 < δ → δ ≤ 1 / 2 →
    1 - δ ≤
      (μ {ω | (∫ t, X 0 t ∂μ) >
        (∑ i, X i ω) / (n + 1 : ℝ) -
          (sampleMax X ω - a) *
            Real.sqrt (Real.log (1 / δ) / (2 * (n + 1 : ℝ)))}).toReal

theorem main : ClaimedBound := by
  sorry

end OMA.S_mo_245620
