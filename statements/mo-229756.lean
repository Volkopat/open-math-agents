import Mathlib

/-!
# MathOverflow 229756

Source: https://mathoverflow.net/questions/229756
-/

namespace OMA.S_mo_229756

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped ENNReal Pointwise Topology

theorem main : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [T2Space G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
      (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegularCompactLTTop],
      ∀ H : Subgroup G, MeasurableSet (H : Set G) → 0 < μ H → μ H ≠ ∞ →
        IsOpen (H : Set G) ∧ IsCompact (H : Set G) := by
  sorry

end OMA.S_mo_229756
