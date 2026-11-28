import OMAReductions.R_InscribedSquare_inscribed_square_problem_R1
import Mathlib

-- Step InscribedSquare.inscribed_square_problem.R1.H1: hypothesis H1 of reduction InscribedSquare.inscribed_square_problem.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Continuity of the measure of translates of a compact set
(`eventually_nhds_zero_measure_vadd_sdiff_lt`) gives, for each of the three shift directions
`(1,0)`, `(1,1)`, `(0,1)`, that `vol (K \ (K - h w)) < vol K / 3` for all small `h`. If no corner
`a ∈ K` had its three shifted corners in `K`, then `K` would be covered by these three sets,
forcing `vol K < vol K`. -/

open Filter MeasureTheory Set Topology
open scoped ENNReal EuclideanGeometry Pointwise

namespace P4ISQ

theorem small_shift (K : Set ℝ²) (hK : IsCompact K) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    (w : ℝ²) : ∀ᶠ h : ℝ in 𝓝 0, volume (K \ ((-(h • w)) +ᵥ K)) < ε := by
  have h1 := eventually_nhds_zero_measure_vadd_sdiff_lt (μ := volume) hK hK.isClosed hε
  have hc : Continuous (fun h : ℝ => h • w) := continuous_id.smul continuous_const
  have hv : Tendsto (fun h : ℝ => h • w) (𝓝 0) (𝓝 0) := hc.tendsto' 0 0 (zero_smul ℝ w)
  filter_upwards [hv.eventually h1] with h hh
  have e : K \ ((-(h • w)) +ᵥ K) = (-(h • w)) +ᵥ (((h • w) +ᵥ K) \ K) := by
    rw [Set.vadd_set_sdiff, neg_vadd_vadd]
  rw [e, measure_vadd]
  exact hh

theorem e1_eq (h : ℝ) : !₂[h, 0] = h • !₂[(1 : ℝ), 0] := by
  ext i; fin_cases i <;> simp

theorem e2_eq (h : ℝ) : !₂[0, h] = h • !₂[(0 : ℝ), 1] := by
  ext i; fin_cases i <;> simp

theorem mem_shift {K : Set ℝ²} {a w : ℝ²} (h : a ∈ (-w) +ᵥ K) : a + w ∈ K := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add] at h
  rwa [add_comm]

end P4ISQ

open P4ISQ in
theorem OMA.solution : OMA.R_InscribedSquare_inscribed_square_problem_R1.H1 := by
  intro K hK hpos
  have hε : volume K / 3 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hpos.ne', by simp⟩
  set w1 : ℝ² := !₂[(1 : ℝ), 0]
  set w3 : ℝ² := !₂[(0 : ℝ), 1]
  filter_upwards [small_shift K hK hε w1, small_shift K hK hε (w1 + w3),
    small_shift K hK hε w3] with h h1 h2 h3
  by_contra hne
  have hsub : K ⊆ (K \ ((-(h • w1)) +ᵥ K)) ∪ (K \ ((-(h • (w1 + w3))) +ᵥ K)) ∪
      (K \ ((-(h • w3)) +ᵥ K)) := by
    intro a ha
    by_contra hn
    simp only [Set.mem_union, Set.mem_sdiff, not_or, not_and, not_not] at hn
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
    apply hne
    refine ⟨a, ha, ?_, ?_, ?_⟩
    · rw [e1_eq]; exact mem_shift (hn1 ha)
    · rw [e1_eq, e2_eq, add_assoc, ← smul_add]; exact mem_shift (hn2 ha)
    · rw [e2_eq]; exact mem_shift (hn3 ha)
  have hle : volume K ≤ volume (K \ ((-(h • w1)) +ᵥ K)) +
      volume (K \ ((-(h • (w1 + w3))) +ᵥ K)) + volume (K \ ((-(h • w3)) +ᵥ K)) :=
    (measure_mono (μ := volume) hsub).trans
      ((measure_union_le (μ := volume) _ _).trans
        (add_le_add (measure_union_le (μ := volume) _ _) le_rfl))
  have hlt : volume (K \ ((-(h • w1)) +ᵥ K)) + volume (K \ ((-(h • (w1 + w3))) +ᵥ K)) +
      volume (K \ ((-(h • w3)) +ᵥ K)) < volume K / 3 + volume K / 3 + volume K / 3 :=
    ENNReal.add_lt_add (ENNReal.add_lt_add h1 h2) h3
  rw [ENNReal.add_thirds] at hlt
  exact lt_irrefl _ (hle.trans_lt hlt)
