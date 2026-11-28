import OMAStatements.S_oeis_a333905
import Mathlib

open OMA.S_oeis_a333905

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a333905.main) := by
  intro h
  have h1 := h.1 8
  have h2 := h.2.1 1
  simp only [lag, numerator] at h1
  norm_num at h1 h2
  linarith
