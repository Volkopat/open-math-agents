import OMAStatements.S_oeis_a219367
import Mathlib

open OMA.S_oeis_a219367

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a219367.main) := by
  intro h
  have h1 := h.1 10
  have h2 := h.2 0
  simp only [lag, numerator] at h1
  norm_num at h1 h2
  linarith
