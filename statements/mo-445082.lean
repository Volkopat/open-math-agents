import Mathlib

/-!
# Product measures and conditioning on a Borel observation

Let f be a Borel map from the square of the unit interval back to the interval.
The finite-cell characterization uses the successive finite Borel partitions
`countablePartition` that generate the Borel sigma-algebra of the output.
For the output cell containing f(ω), `cellMass` is the proportion of its
preimage occupied by a specified event. Conditional independence holds exactly
when the difference between the joint proportion and the product of the two
marginal proportions tends to zero almost surely for every pair of coordinate
events. This test involves only the original product law and sets defined by f.

Rectangular Borel fibres are necessary for preserving independence under all
product laws. For maps of countable image they are also sufficient. For general
maps the proposed sufficiency is false even for independent uniform inputs.
The counterexample encodes each input as an affine line. Their intersection
has rectangular fibres. The Jacobian for a pair of slopes gives a nonproduct
conditional distribution on a region of positive probability.

Source: Matthias Georg Mayer, https://mathoverflow.net/questions/445082
(CC BY-SA 4.0). The two-point necessity argument is due to the questioner.
The finite-cell criterion uses Lévy's upward theorem.
Credit: @connoranderson (agent: Codex).
-/
namespace OMA.S_mo_445082
open MeasureTheory Set ProbabilityTheory
abbrev I := Set.Icc (0:ℝ) 1
abbrev Plane := Fin 2 → ℝ
def rectangular (Z : I × I → I) : Prop := ∀ z, ∃ A B : Set I,
  MeasurableSet A ∧ MeasurableSet B ∧ Z ⁻¹' {z} = A ×ˢ B
def preserves (f : I × I → I) (hf : Measurable f) : Prop :=
  ∀ (μ ν : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    CondIndepFun (MeasurableSpace.comap f inferInstance) hf.comap_le
      (Prod.fst : I × I → I) Prod.snd (μ.prod ν)
noncomputable def cellMass (P : Measure (I × I)) (f : I × I → I) (A : Set (I × I))
    (n : ℕ) (ω : I × I) : ℝ :=
  let C := f ⁻¹' MeasurableSpace.countablePartitionSet n (f ω)
  P.real (C ∩ A) / P.real C
def cellTest (μ ν : Measure I) (f : I × I → I) : Prop :=
  ∀ A B : Set I, MeasurableSet A → MeasurableSet B → ∀ᵐ ω ∂μ.prod ν,
    Filter.Tendsto (fun n => cellMass (μ.prod ν) f (A ×ˢ B) n ω -
      cellMass (μ.prod ν) f (Prod.fst ⁻¹' A) n ω * cellMass (μ.prod ν) f (Prod.snd ⁻¹' B) n ω)
      Filter.atTop (nhds 0)
end OMA.S_mo_445082
namespace OMA.S_mo_445082
open ProbabilityTheory MeasureTheory Set
theorem main :
    (∀ (f : I × I → I) (hf : Measurable f) (μ ν : Measure I) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      CondIndepFun (MeasurableSpace.comap f inferInstance) hf.comap_le
        (Prod.fst : I × I → I) Prod.snd (μ.prod ν) ↔ cellTest μ ν f) ∧
    (∀ (f : I × I → I) (hf : Measurable f), preserves f hf → rectangular f) ∧
    (∀ (f : I × I → I) (hf : Measurable f), (range f).Countable → (rectangular f ↔ preserves f hf)) ∧
    (∃ (f : I × I → I) (hf : Measurable f), rectangular f ∧
      ¬CondIndepFun (MeasurableSpace.comap f inferInstance) hf.comap_le
        (Prod.fst : I × I → I) Prod.snd ((volume : Measure I).prod volume)) := by
  sorry
end OMA.S_mo_445082
