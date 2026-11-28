import Mathlib

/-!
# A Gaussian-channel counterexample to a proposed MMSE inequality

Source: math-Student, https://mathoverflow.net/questions/232822 (CC BY-SA 3.0).
Credit: @connoranderson.

Let Y, N, E be independent standard Gaussian variables. Put X = Y²+E and
Z = Y+N, so the signal-to-noise parameter is one. The pair (X,Y) has a joint
density. X alone gives conditional mean zero for Y, but it strictly improves
the estimate using Z. The proposed mutual-information bound also fails.
Here mmse is the mean squared residual from the conditional expectation,
equivalently the expectation of the conditional variance as in the question.
-/

namespace OMA.S_mo_232822
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

abbrev Ω := ℝ × (ℝ × ℝ)
noncomputable def law : Measure Ω := (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))

instance law_probability : IsProbabilityMeasure law := by unfold law; infer_instance

def Y (ω : Ω) : ℝ := ω.1
def X (ω : Ω) : ℝ := ω.1^2+ω.2.2
def Z (ω : Ω) : ℝ := ω.1+ω.2.1

abbrev mX : MeasurableSpace Ω := MeasurableSpace.comap X (borel ℝ)
abbrev mZ : MeasurableSpace Ω := MeasurableSpace.comap Z (borel ℝ)

noncomputable def mmse (m : MeasurableSpace Ω) : ℝ :=
  ∫ ω, (Y ω - (law[Y | m]) ω)^2 ∂law

noncomputable def info (U V : Ω → ℝ) : ℝ≥0∞ :=
  klDiv (law.map (fun ω => (U ω,V ω))) ((law.map U).prod (law.map V))

theorem main :
    (law.map (fun ω => (X ω,Y ω))) ≪ volume ∧
    law.map (fun ω : Ω => ω.2.1) = gaussianReal 0 1 ∧
    IndepFun (fun ω : Ω => ω.2.1) (fun ω => (X ω,Y ω)) law ∧
    mmse mX = variance Y law ∧ variance Y law = 1 ∧ mmse mZ = 1/2 ∧
    mmse (mX ⊔ mZ)/mmse mZ < mmse mX/variance Y law ∧
    ENNReal.ofReal (1-mmse mX/variance Y law)*info Y Z < info X Z := by
  sorry

end OMA.S_mo_232822
