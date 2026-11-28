import OMAReductions.R_Erdos743_erdos_743_variants_bounded_degree_R1

-- Original proof: @caa1982. Cross-multiplication argument: @menelikbaye-digitalmethod.

open Filter in
theorem OMA.solution : OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1.H2 := by
  intro c hc d
  have hlimit := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  have hd : (0 : ℝ) < d + 1 := by positivity
  filter_upwards [hlimit.eventually (gt_mem_nhds (div_pos hc hd)),
    eventually_ge_atTop 2] with n hratio hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hcross := (div_lt_div_iff₀ hn0 hd).mp hratio
  rw [le_div_iff₀ hlog]
  linarith only [hcross, hlog]
