import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1
import Mathlib

-- Step Erdos835.erdos_835.variants.johnson.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction
-- Erdos835.erdos_835.variants.johnson.R1.H1.R1.H1.R1
-- Credit: @ivillar. The reduction file itself proves H2 as `binary_implications`; this step applies it.

/-! Satisfiability of consistent binary implication systems. -/

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1.H2 :=
  OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1.binary_implications
