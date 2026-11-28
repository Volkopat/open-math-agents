import OMAStatements.S_oeis_a219211
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a219211.main) := by
  intro h
  have h1 := h.1 7
  have h2 := h.2 7 (by norm_num)
  simp [OMA.S_oeis_a219211.lag, OMA.S_oeis_a219211.numerator] at h1
  norm_num at h2
  linarith
