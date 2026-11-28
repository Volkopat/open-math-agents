import Mathlib

/-!
# Upper bound of conditional mutual information

Source https://mathoverflow.net/questions/432767
Credit @Denyven

The question fixes the joint law of two random variables and asks for the
supremum of their conditional mutual information over auxiliary variables.
An auxiliary law `ν` and its conditional joint law `κ` form an extension
precisely when the mixture `κ ∘ₘ ν` is the specified joint law.
Conditional information uses relative entropy, which agrees with the source's
Shannon entropy identity when the latter is defined.

The expression on the right minimizes an expectation over nonnegative weights
on the atoms of the two marginals, with total weight at most one. A zero
denominator makes the integrand infinite. On discrete alphabets the expectation
is the sum of `p (x,y) * log (1 / (u x + v y))` over positive cells.
-/

namespace OMA.S_mo_432767

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

universe u v w

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]

noncomputable def jointInformation (P : Measure (X × Y)) : ℝ≥0∞ :=
  klDiv P ((P.map Prod.fst).prod (P.map Prod.snd))

noncomputable def conditionalInformation {Z : Type w} [MeasurableSpace Z]
    (ν : Measure Z) (κ : Kernel Z (X × Y)) : ℝ≥0∞ :=
  ∫⁻ z, jointInformation (κ z) ∂ν

noncomputable def auxiliaryValues (P : Measure (X × Y)) : Set ℝ≥0∞ :=
  {r | ∃ (Z : Type w) (mZ : MeasurableSpace Z),
    letI := mZ
    ∃ (ν : Measure Z) (κ : Kernel Z (X × Y)),
      IsProbabilityMeasure ν ∧ IsMarkovKernel κ ∧ κ ∘ₘ ν = P ∧ r = conditionalInformation ν κ}

def admissibleBudget (P : Measure (X × Y)) (row : X → ℝ≥0) (column : Y → ℝ≥0) : Prop :=
  Measurable row ∧ Measurable column ∧
    (∀ x, P.map Prod.fst {x} = 0 → row x = 0) ∧
    (∀ y, P.map Prod.snd {y} = 0 → column y = 0) ∧
    (∑' x, (row x : ℝ≥0∞)) + (∑' y, (column y : ℝ≥0∞)) ≤ 1

noncomputable def budgetCost (P : Measure (X × Y)) (row : X → ℝ≥0) (column : Y → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ xy, if row xy.1 + column xy.2 = 0 then ∞
    else ENNReal.ofReal (-Real.log ((row xy.1 + column xy.2 : ℝ≥0) : ℝ)) ∂P

theorem main :
    ∀ [StandardBorelSpace X] [StandardBorelSpace Y] (P : Measure (X × Y)) [IsProbabilityMeasure P],
    ∃ (row : X → ℝ≥0) (column : Y → ℝ≥0),
      admissibleBudget P row column ∧
      (∀ row' column', admissibleBudget P row' column' → budgetCost P row column ≤ budgetCost P row' column') ∧
      sSup (auxiliaryValues.{u, v, w} P) = budgetCost P row column := by
  sorry

end OMA.S_mo_432767
