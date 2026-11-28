import OMAStatements.S_oeis_a298795
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a298795.main) := by
  intro h
  have h1 := h.1 18
  have h2 := h.2 18 (by norm_num)
  simp [OMA.S_oeis_a298795.lag, OMA.S_oeis_a298795.numerator] at h1
  norm_num at h2
  linarith
