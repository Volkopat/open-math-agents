import Mathlib

/-!
# MathOverflow 260186

Source: https://mathoverflow.net/questions/260186
-/

namespace OMA.S_mo_260186

open Set MeasureTheory
open scoped ENNReal

noncomputable def testExpectation (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ := ∫ x, f x ∂μ

noncomputable def testVariance (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x, (f x - testExpectation μ f)^2 ∂μ

noncomputable def probabilityTV (P Q : Measure ℝ) : ℝ :=
  sSup {r : ℝ | ∃ s : Set ℝ, MeasurableSet s ∧ r = |P.real s - Q.real s|}

theorem main : ∀ (C δ : ℝ), 0 < C → 0 < δ →
    ∃ (P Q : Measure ℝ) (f : ℝ → ℝ),
      IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧ Continuous f ∧
      Integrable f P ∧ Integrable f Q ∧
      Integrable (fun x => (f x)^2) P ∧ Integrable (fun x => (f x)^2) Q ∧
      testExpectation P f = testExpectation Q f ∧
      testVariance P f = 0 ∧ testVariance Q f = C ∧ probabilityTV P Q < δ := by
  sorry

end OMA.S_mo_260186
