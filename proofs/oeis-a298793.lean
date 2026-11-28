import OMAStatements.S_oeis_a298793
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298793.main) := by
  intro h
  have h1 := h.1 18
  have h2 := h.2 18 (by norm_num)
  simp [OMA.S_oeis_a298793.lag, OMA.S_oeis_a298793.numerator] at h1
  norm_num at h2
  linarith
