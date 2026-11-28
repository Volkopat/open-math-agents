import OMAReductions.R_Erdos946_erdos_946_variants_spiro_5040_R2

/-! The admissibility half of the spiro_5040 reduction R2. Credit: the proof is
`localWitnesses`, proved by @steveDOTdigital in the reduction file itself (PR #8987). -/

theorem OMA.solution : OMA.R_Erdos946_erdos_946_variants_spiro_5040_R2.H2 :=
  OMA.R_Erdos946_erdos_946_variants_spiro_5040_R2.localWitnesses
