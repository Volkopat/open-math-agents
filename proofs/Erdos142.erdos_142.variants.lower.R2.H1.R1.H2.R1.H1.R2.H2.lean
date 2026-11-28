import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2
import Mathlib

-- Step Erdos142.erdos_142.variants.lower.R2.H1.R1.H2.R1.H1.R2.H2 (a modular progression inside
-- the image of a short interval lifts to a positive-step progression of integers).
-- Stated plainly: the reduction file itself already proves this hypothesis, as the theorem
-- lift_progression in its own namespace. This file adds no mathematics; it only points at that
-- theorem. All credit for the proof goes to the author of the reduction.

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2.H2 :=
  OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R1_H1_R2.lift_progression
