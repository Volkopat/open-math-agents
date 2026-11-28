import Mathlib

/-!
# Topological Space of Cardinality kappa Containing All Metric Spaces of Cardinality kappa

Source: https://math.stackexchange.com/questions/4084662/is-there-a-topological-space-of-cardinality-kappa-containing-all-metric-space
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
It is known that all countable metrizable spaces embed into `ℚ`, and by Kowalski's
theorem, for any infinite cardinal `κ` satisfying `κ ^ ℵ₀ = κ`, there exists a
topological space of cardinality `κ` into which every metrizable space of
cardinality `κ` embeds.

Is there an uncountable cardinal `κ` with `κ ^ ℵ₀ ≠ κ` and a topological space `X`
of cardinality `κ` such that every metrizable space of cardinality `κ` embeds
topologically into `X`?

## Formalization Notes
We work in universe `Type` (`Cardinal.{0}`) and quantify over all metric spaces
`(Y : Type)` with `Cardinal.mk Y = κ`, requiring a topological embedding
`Topology.IsEmbedding f` for some `f : Y → X`.
-/

namespace OMA.S_mse_4084662

theorem main :
    ∃ (κ : Cardinal.{0}), Cardinal.aleph0 < κ ∧ κ ^ Cardinal.aleph0 ≠ κ ∧
      ∃ (X : Type) (_ : TopologicalSpace X),
        Cardinal.mk X = κ ∧
        ∀ (Y : Type) [MetricSpace Y], Cardinal.mk Y = κ →
          ∃ f : Y → X, Topology.IsEmbedding f := by
  sorry

end OMA.S_mse_4084662
