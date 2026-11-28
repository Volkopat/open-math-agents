import Mathlib
import Mathlib.Probability.BrownianMotion.Basic

/-!
# Jordan arcs crossing a planar Brownian trace finitely often

Krzysztof Burdzy, "My favorite open problems", Problem 2(i).
https://sites.math.washington.edu/~burdzy/open_mathjax.php
Credit: @pmaster

Planar Brownian motion has two independent standard real Brownian coordinates.
A continuous injection of the compact unit interval into the plane is a
homeomorphism onto its image. The source asks that the arc contain both points.
-/

namespace OMA.S_burdzy_brownian_trace_arcs_finite_intersection

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

abbrev Plane := ℝ × ℝ

def Trace {Ω : Type} (X Y : ℝ≥0 → Ω → ℝ) (ω : Ω) : Set Plane :=
  (fun t => (X t ω, Y t ω)) '' Set.Icc 0 1

def FiniteArcCrossing (K : Set Plane) : Prop :=
  ∀ x ∉ K, ∀ y ∉ K,
    ∃ γ : Set.Icc (0 : ℝ) 1 → Plane,
      Continuous γ ∧ Function.Injective γ ∧
      x ∈ Set.range γ ∧ y ∈ Set.range γ ∧ (Set.range γ ∩ K).Finite

theorem main : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ), IsBrownianReal X P → IsBrownianReal Y P →
    IndepFun (fun ω t => X t ω) (fun ω t => Y t ω) P →
    ∀ᵐ ω ∂P, FiniteArcCrossing (Trace X Y ω) := by
  sorry

end OMA.S_burdzy_brownian_trace_arcs_finite_intersection
