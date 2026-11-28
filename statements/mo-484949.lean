import Mathlib

namespace OMA.S_mo_484949

universe u

/-- A metric space with only rational distances has a compatible ultrametric. -/
theorem main :
    ∀ (X : Type u) (metric : MetricSpace X),
      (∀ x y : X, ∃ q : ℚ, (q : ℝ) = metric.toPseudoMetricSpace.toDist.dist x y) →
      ∃ ultra : MetricSpace X,
        @IsUltrametricDist X ultra.toPseudoMetricSpace.toDist ∧
          ultra.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
            metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  sorry

end OMA.S_mo_484949
