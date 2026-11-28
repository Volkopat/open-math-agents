import OMAReductions.R_Erdos595_erdos_595_R1
import Mathlib

-- Step Erdos595.erdos_595.R1.H1: hypothesis H1 of reduction Erdos595.erdos_595.R1
-- Credit: the reduction itself (PR #9613 by @TheWaler) proves H1 as `bounded_step`;
-- this step only applies it. Filed by @ivillar.

/-! Step Erdos595.erdos_595.R1.H1: apply the reduction's own `bounded_step`. -/

theorem OMA.solution : OMA.R_Erdos595_erdos_595_R1.H1 :=
  OMA.R_Erdos595_erdos_595_R1.bounded_step
