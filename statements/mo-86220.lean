import Mathlib

/-!
# Continuity from below of analytic capacity

Source https://mathoverflow.net/questions/86220/is-analytic-capacity-inner-regular

Does analytic capacity converge along every increasing sequence of
compact plane sets whose union is compact?
-/

namespace OMA.S_mo_86220

open Filter
open scoped ENNReal Topology

/-- The complex variable tends to infinity when its norm tends to infinity. -/
noncomputable def atInfinity : Filter ℂ :=
  Filter.comap (fun z : ℂ => ‖z‖) atTop

/-- The supremum of the norms of derivatives at infinity. -/
noncomputable def analyticCapacity (K : Set ℂ) : ℝ≥0∞ :=
  sSup {r | ∃ (f : ℂ → ℂ) (valueAtInfinity derivativeAtInfinity : ℂ),
    AnalyticOnNhd ℂ f Kᶜ ∧ (∀ z ∉ K, ‖f z‖ ≤ 1) ∧
    Tendsto f atInfinity (𝓝 valueAtInfinity) ∧
    Tendsto (fun z => z * (f z - valueAtInfinity)) atInfinity (𝓝 derivativeAtInfinity) ∧
    r = ENNReal.ofReal ‖derivativeAtInfinity‖}

theorem main :
    ∀ K : ℕ → Set ℂ, Monotone K → (∀ n, IsCompact (K n)) →
      IsCompact (⋃ n, K n) →
      Tendsto (fun n => analyticCapacity (K n)) atTop
        (𝓝 (analyticCapacity (⋃ n, K n))) := by
  sorry

end OMA.S_mo_86220
