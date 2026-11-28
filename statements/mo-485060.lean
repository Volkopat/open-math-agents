import Mathlib

/-!
# Certainty of events and Dirac conditional laws

The question asks whether every positive-mass Borel set can contain the
conditional outcome with certainty on a positive-mass set of observations only
if a positive-mass set of observations has a Dirac conditional law.

For any prescribed real probability marginal μ, encode two independent draws
from μ in the observed real variable, then choose one of them with equal
probabilities. The set of observations giving certainty to A has mass μ(A)².
The Dirac conditionals have mass equal to the diagonal mass of μ × μ.
Taking an atomless marginal disproves the proposed implication. For arbitrary
couplings the implication does hold when the marginal has a positive atom.

Source: thibault_student, https://mathoverflow.net/questions/485060
(CC BY-SA 4.0). The atomic case is identified in the source.
Credit: @connoranderson (agent: Codex).
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace OMA.S_mo_485060

/-- In the joint measure π the conditioning coordinate Y comes first. -/
def certainty (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π] (A : Set ℝ) : Set ℝ :=
  {y | π.condKernel y A = 1}

def diracPoints (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π] : Set ℝ :=
  {y | ∃ x : ℝ, π.condKernel y = Measure.dirac x}

theorem main :
    (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
      ∃ (π : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure π), π.snd = μ ∧
        (∀ A : Set ℝ, MeasurableSet A → π.fst (certainty π A) = (μ A)^2) ∧
        π.fst (diracPoints π) = (μ.prod μ) (diagonal ℝ)) ∧
    (∃ (π : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure π),
      (∀ A : Set ℝ, MeasurableSet A → 0 < π.snd A → 0 < π.fst (certainty π A)) ∧
      π.fst (diracPoints π) = 0) ∧
    (∀ (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π],
      (∀ A : Set ℝ, MeasurableSet A → 0 < π.snd A → 0 < π.fst (certainty π A)) →
      (∃ z : ℝ, 0 < π.snd {z}) → 0 < π.fst (diracPoints π)) := by
  sorry
end OMA.S_mo_485060
