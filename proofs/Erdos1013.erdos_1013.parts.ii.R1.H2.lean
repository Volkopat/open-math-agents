import OMAReductions.R_Erdos1013_erdos_1013_parts_ii_R1

/-!
# Step H2 of the reduction Erdos1013.erdos_1013.parts.ii.R1

For `c > 0`, `c (k+1)^2 log (k+1) / (c k^2 log k) → 1`. Eventually the ratio is
`((k+1)/k)^2 * (1 + log ((k+1)/k) / log k)`; the first factor tends to `1`, and in the second
`log ((k+1)/k) → 0` while `log k → ∞`.
-/

open Filter Topology

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_parts_ii_R1.H2 := by
  intro c hc
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- `(k + 1) / k → 1`
  have hq : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / k) atTop (𝓝 1) := by
    have h0 : Tendsto (fun k : ℕ => 1 + 1 / (k : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
  -- `log ((k + 1) / k) → 0`
  have hlq : Tendsto (fun k : ℕ => Real.log (((k : ℝ) + 1) / k)) atTop (𝓝 0) := by
    have := ((Real.continuousAt_log one_ne_zero).tendsto).comp hq
    rw [Real.log_one] at this
    exact this
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hr : Tendsto (fun k : ℕ => 1 + Real.log (((k : ℝ) + 1) / k) / Real.log k) atTop
      (𝓝 (1 + 0)) := tendsto_const_nhds.add (hlq.div_atTop hlog)
  rw [add_zero] at hr
  have hlim : Tendsto (fun k : ℕ => (((k : ℝ) + 1) / k) ^ 2 *
      (1 + Real.log (((k : ℝ) + 1) / k) / Real.log k)) atTop (𝓝 1) := by
    have := (hq.pow 2).mul hr
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with k hk
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hlk : Real.log (k : ℝ) ≠ 0 := (Real.log_pos hkR).ne'
  have hsplit : Real.log (((k : ℝ) + 1) / k) = Real.log ((k : ℝ) + 1) - Real.log k :=
    Real.log_div hk1 hk0
  rw [hsplit]
  push_cast
  field_simp
  ring
