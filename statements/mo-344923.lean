import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Mutual information under a nonexpansive map

Source: https://mathoverflow.net/questions/344923
Question by minimore99, 30 October 2019. Credit: @etaubman.

The question asks whether a 1-Lipschitz map necessarily preserves mutual
information. The author's final comment explicitly clarifies that injectivity
is not assumed. This statement concerns that assertion, not the separate
observation about invertible measurable transformations.

The metric spaces carry their Borel sigma-algebras. A pair of random variables
is represented by its joint probability law on the product space; conversely,
the coordinate maps realize every such law. Mutual information is the
Kullback-Leibler divergence of the joint law from the product of its marginals.
Mathlib's nonnegative extended-real divergence agrees with the usual mutual
information for probability measures, including the possible value infinity.
No finiteness, discreteness, or independence hypothesis is imposed.
-/

open MeasureTheory
open scoped ENNReal

namespace OMA.S_mo_344923

noncomputable def mutualInformation {A : Type*} [MeasurableSpace A]
    (μ : Measure (A × A)) : ℝ≥0∞ :=
  InformationTheory.klDiv μ (μ.fst.prod μ.snd)

theorem main :
    ∀ (A B : Type) [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
      [MetricSpace B] [MeasurableSpace B] [BorelSpace B]
      (μ : Measure (A × A)), IsProbabilityMeasure μ →
      ∀ f : A → B, LipschitzWith 1 f →
        mutualInformation (μ.map (fun z => (f z.1, f z.2))) =
          mutualInformation μ := by
  sorry

end OMA.S_mo_344923
