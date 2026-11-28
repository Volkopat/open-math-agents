import OMAStatements.S_oeis_a059837
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a059837.main) :=
  fun h => absurd (h 0) (by decide +kernel)
