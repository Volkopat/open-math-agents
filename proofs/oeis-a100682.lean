import OMAStatements.S_oeis_a100682
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a100682.main) :=
  fun h => absurd (h 2 (by decide)) (by decide +kernel)
