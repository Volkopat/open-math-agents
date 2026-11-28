import OMAReductions.R_Erdos1081_erdos_1081_R1

open Filter in
theorem OMA.solution : OMA.R_Erdos1081_erdos_1081_R1.H2 := fun a C ha =>
  ((tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2
    ⟨(isLittleO_log_rpow_rpow_atTop C ha).tendsto_div_nhds_zero, by
      filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0, eventually_gt_atTop 0] with y h g
      exact div_pos (Real.rpow_pos_of_pos h C) (Real.rpow_pos_of_pos g a)⟩)).congr
    fun _ => inv_div _ _).comp Real.tendsto_log_atTop
