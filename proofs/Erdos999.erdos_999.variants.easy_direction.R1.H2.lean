import OMAReductions.R_Erdos999_erdos_999_variants_easy_direction_R1

/-! # Borel–Cantelli on the unit interval -/
-- Credit: @steveDOTdigital

open MeasureTheory

theorem OMA.solution : OMA.R_Erdos999_erdos_999_variants_easy_direction_R1.H2 := by
  intro s g hsum hbound hinfinite
  have hfinite := ae_finite_setOfPred_mem
    (ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hbound))
  have hzero := ae_iff.mp ((hfinite.and hinfinite).mono fun _ ⟨hf, hi⟩ => hi hf)
  simp [Real.volume_Icc] at hzero
