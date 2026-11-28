import OMAStatements.S_oeis_a050446
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a050446.main) :=
  fun h => absurd (h 1 1) (by decide +kernel)
