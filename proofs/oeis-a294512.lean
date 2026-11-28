import OMAStatements.S_oeis_a294512
import Mathlib

namespace OMA.Helpers_a294512

open OMA.S_oeis_a294512

theorem counter : ¬ ((a 164 : ℚ) = (b (164 + 1) : ℚ) / (((164 : ℕ) : ℚ) + 1)) := by
  decide +kernel

end OMA.Helpers_a294512

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a294512.main) := fun h =>
  OMA.Helpers_a294512.counter (h 164)
