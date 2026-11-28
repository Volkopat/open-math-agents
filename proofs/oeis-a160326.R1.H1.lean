import OMAReductions.R_oeis_a160326_R1
import Mathlib

theorem OMA.solution : OMA.R_oeis_a160326_R1.H1 := by
  intro n h
  exact Nat.eq_sq_add_sq_iff.mpr h
