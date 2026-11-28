import OMAStatements.S_mo_479120
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_479120.main) := by
  intro h
  have hupper := (h 1 10 1 (by decide) (by decide) (by decide)).2
  have hvalue : OMA.S_mo_479120.a 1 10 1 = 12 := by decide +kernel
  rw [hvalue] at hupper
  omega