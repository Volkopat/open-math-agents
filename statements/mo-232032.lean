import Mathlib

/-!
# Does a decrease in Jensen–Shannon divergence imply a decrease in KL divergence?

Jack Cheng, MathOverflow question 232032 (2016), CC BY-SA.
https://mathoverflow.net/questions/232032
Lean formalization by @rifter0418.

A decrease compares a before pair and an after pair on the same measurable
space. The comparison is strict, and KL is taken in the order P relative to Q.
The pairs may share their first distribution. Mathlib's KL divergence uses
natural logarithms and allows the value infinity.
-/

namespace OMA.S_mo_232032

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

universe u

/-- The equal mixture of two measures. -/
noncomputable def mixture {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : Measure Ω :=
  (2 : ℝ≥0)⁻¹ • (P + Q)

/-- The equally weighted Jensen–Shannon divergence from the question. -/
noncomputable def jsDiv {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ≥0∞ :=
  (klDiv P (mixture P Q) + klDiv Q (mixture P Q)) / 2

theorem main :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P₀ Q₀ P₁ Q₁ : ProbabilityMeasure Ω),
      jsDiv (P₁ : Measure Ω) Q₁ < jsDiv (P₀ : Measure Ω) Q₀ →
      klDiv (P₁ : Measure Ω) Q₁ < klDiv (P₀ : Measure Ω) Q₀ := by
  sorry

end OMA.S_mo_232032
