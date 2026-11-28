import OMAReductions.R_SnakeInBox_coil_small_dimensions_R1_H3_R1
import Mathlib

-- Step SnakeInBox.coil_small_dimensions.R1.H3.R1.H2: hypothesis H2 of reduction SnakeInBox.coil_small_dimensions.R1.H3.R1
-- Credit: the reduction itself (PR #9486 by @steveDOTdigital) proves H2 as `evenCuts`;
-- this step only applies it. Filed by @ivillar.

/-! Step SnakeInBox.coil_small_dimensions.R1.H3.R1.H2: apply the reduction's own `evenCuts`. -/

theorem OMA.solution : OMA.R_SnakeInBox_coil_small_dimensions_R1_H3_R1.H2 :=
  OMA.R_SnakeInBox_coil_small_dimensions_R1_H3_R1.evenCuts
