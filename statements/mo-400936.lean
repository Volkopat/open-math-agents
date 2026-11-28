import Mathlib

/-!
# Positive covariance for exponential transformations with a common variable

Source: A.E. Charman, [Weak sufficient conditions for non-negative correlation between
functions of correlated random variables?](https://mathoverflow.net/questions/400936)
(2021, CC BY-SA 4.0). Credit: @connoranderson (agent: Codex).

The joint law has coordinates (X,(A,B)), all taking nonnegative real values.
A product of the law of X with the joint law of (A,B) expresses independence
of X from that pair. The two equivalences characterize the pairs for which
the source covariances are nonnegative for **every** independent X. Their
conditions test the same Laplace parameter on A and B. A finite example
satisfies all these tests despite failing positive quadrant dependence.

For arbitrary dependence the quantitative lower bounds give sufficient
conditions involving the separation of A and B. Each bound subtracts
the expected squared, clipped separation from the sum of the two
transformed variances. The last example has exact positive Pearson
correlation one for A,B, and both transformed covariances are negative.
-/

open MeasureTheory Set
open scoped NNReal ENNReal
namespace OMA.S_mo_400936
abbrev S := ℝ≥0
abbrev Pair := S × S
abbrev Triple := S × Pair

noncomputable def cov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) :=
  (∫ x, f x*g x ∂μ) - (∫ x, f x ∂μ)*(∫ x, g x ∂μ)

noncomputable def lap (x a : S) := Real.exp (-(x:ℝ)*(a:ℝ))
noncomputable def addExp (x a : S) := Real.exp (-(x:ℝ)-(a:ℝ))

noncomputable def pairCov (μ : Measure Pair) (h g : S → ℝ) :=
  cov μ (fun z => h z.1) (fun z => g z.2)

noncomputable def sharedCov (ρ : Measure Triple) (K : S → S → ℝ) :=
  cov ρ (fun z => K z.1 z.2.1) (fun z => K z.1 z.2.2)

noncomputable def lowerEvent (t a : S) : ℝ := if a ≤ t then 1 else 0

def PQD (μ : Measure Pair) : Prop := ∀ s t, 0 ≤ pairCov μ (lowerEvent s) (lowerEvent t)

noncomputable def firstValue (z : Triple) : ℝ := z.2.1
noncomputable def secondValue (z : Triple) : ℝ := z.2.2

noncomputable def pearson (ρ : Measure Triple) : ℝ :=
  cov ρ firstValue secondValue /
    Real.sqrt (cov ρ firstValue firstValue * cov ρ secondValue secondValue)

noncomputable def covarianceLower (ρ : Measure Triple) (K : S → S → ℝ) (slope : S → ℝ) : ℝ :=
  cov ρ (fun z => K z.1 z.2.1) (fun z => K z.1 z.2.1) +
  cov ρ (fun z => K z.1 z.2.2) (fun z => K z.1 z.2.2) -
  ∫ z, (min 1 (slope z.1 * |firstValue z - secondValue z|))^2 ∂ρ

theorem main :
    (∀ (μ : Measure Pair) [IsProbabilityMeasure μ],
      ((∀ (ν : Measure S) [IsProbabilityMeasure ν], 0 ≤ sharedCov (ν.prod μ) lap) ↔
        ∀ t, 0 ≤ pairCov μ (lap t) (lap t)) ∧
      ((∀ (ν : Measure S) [IsProbabilityMeasure ν], 0 ≤ sharedCov (ν.prod μ) addExp) ↔
        0 ≤ pairCov μ (lap 1) (lap 1))) ∧
    (∃ μ : Measure Pair, IsProbabilityMeasure μ ∧ ¬ PQD μ ∧
      ∀ t, pairCov μ (lap t) (lap t) = 0) ∧
    (∀ (ρ : Measure Triple) [IsProbabilityMeasure ρ],
      covarianceLower ρ lap (fun x => (x:ℝ)) ≤ 2*sharedCov ρ lap ∧
      covarianceLower ρ addExp (fun _ => 1) ≤ 2*sharedCov ρ addExp) ∧
    (∃ ρ : Measure Triple, IsProbabilityMeasure ρ ∧
      0 < cov ρ firstValue firstValue ∧ 0 < cov ρ secondValue secondValue ∧ pearson ρ = 1 ∧
      sharedCov ρ lap < 0 ∧ sharedCov ρ addExp < 0) := by
  sorry

end OMA.S_mo_400936
