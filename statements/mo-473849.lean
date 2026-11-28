import Mathlib

/-!
# Topological meaning of a totally recurrent 1d foliation in 3-manifold

Source: MathOverflow (not formalized), https://mathoverflow.net/questions/473849
Credit: @eltociear

The question (Tali, 2024), about D. Sullivan, *Cycles for the dynamical study of foliated
manifolds and complex manifolds* (Invent. Math. 36, 1976): the recurrence set `P(F)` of a
foliation `F` is the union of the supports of all foliation cycles (invariant transverse
measures), and `F` is totally recurrent when `P(F) = M`. Suppose a flow on the 3-manifold `M`
has every point nonwandering (for every open neighbourhood there is a time when it comes back
and meets itself). Would the foliation by the flow lines be totally recurrent?

Reading used here (the standard one, in Sullivan's setting):
* `M` is a closed (compact, boundaryless) smooth 3-manifold and the flow is the flow of a smooth
  nowhere vanishing vector field, so that the flow lines form a smooth oriented 1-dimensional
  foliation. The flow `ϕ` is smooth jointly in `(t, x)` and `d/dt ϕ t x` at `t = 0` is nonzero.
* For such a flow, Sullivan identifies the foliation cycles of the flow-line foliation with the
  finite invariant measures of the flow, so `P(F)` is the union of the supports of the
  `ϕ`-invariant Borel probability measures (normalising a nonzero finite measure does not change
  its support).
* Nonwandering is the usual notion: for every neighbourhood `U` of `x` and every `T`, some
  `t > T` has `ϕ t '' U ∩ U` nonempty (with only `t ≠ 0` the condition would hold trivially).

The statement is the affirmative answer to the question; a disproof is a counterexample flow.
-/

open scoped Manifold ContDiff

namespace OMA.S_mo_473849

/-- `x` is a nonwandering point of the flow `ϕ`. -/
def IsNonwandering {M : Type*} [TopologicalSpace M] (ϕ : Flow ℝ M) (x : M) : Prop :=
  ∀ U ∈ nhds x, ∀ T : ℝ, ∃ t > T, (ϕ t '' U ∩ U).Nonempty

/-- Sullivan's recurrence set of the flow-line foliation: the union of the supports of all
`ϕ`-invariant Borel probability measures. -/
def recurrenceSet {M : Type*} [TopologicalSpace M] [MeasurableSpace M] (ϕ : Flow ℝ M) : Set M :=
  ⋃ (μ : MeasureTheory.Measure M) (_ : MeasureTheory.IsProbabilityMeasure μ)
    (_ : ∀ t : ℝ, MeasureTheory.MeasurePreserving (ϕ t) μ μ), μ.support

theorem main :
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] (ϕ : Flow ℝ M),
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun p : ℝ × M => ϕ p.1 p.2) →
      (∀ x : M, mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun t : ℝ => ϕ t x) 0 ≠ 0) →
      (∀ x : M, IsNonwandering ϕ x) →
      recurrenceSet ϕ = Set.univ := by
  sorry

end OMA.S_mo_473849
