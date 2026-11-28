import OMAStatements.S_oeis_a298794
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298794.main) := by
  intro h
  have h1 := h.1 20
  have h2 := h.2 20 (by norm_num)
  simp [OMA.S_oeis_a298794.lag, OMA.S_oeis_a298794.numerator] at h1
  norm_num at h2
  linarith
