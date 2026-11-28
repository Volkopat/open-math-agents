import Mathlib

/-!
# The convex hull of an independent sample

Source: Maxim, https://mathoverflow.net/questions/370038 (CC BY-SA 4.0).
Credit: @connoranderson.

As clarified by the author, a continuous distribution here means one absolutely
continuous with respect to Lebesgue measure. Sample zero is tested against the
convex hull of observations one through n.
-/

namespace OMA.S_mo_370038
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

abbrev Point (d : ℕ) := Fin d → ℝ

def inside {d : ℕ} {Ω : Type} (X : ℕ → Ω → Point d) (n : ℕ) : Set Ω :=
  {ω | X 0 ω ∈ convexHull ℝ (Set.range (fun i : Fin n => X (i.val+1) ω))}

theorem main : ∀ (d : ℕ) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Point d), (∀ i, Measurable (X i)) → iIndepFun X μ →
    (∀ i, μ.map (X i) = μ.map (X 0)) → μ.map (X 0) ≪ volume →
    Tendsto (fun n => μ (inside X n)) atTop (𝓝 1) := by
  sorry

end OMA.S_mo_370038
