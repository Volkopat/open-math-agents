import OMAStatements.S_oeis_a165105
import Mathlib

/-!
# A165105: the lag identity fails at `n = 2`

For `n = 2` only the lags `0` and `1` contribute, so the identity reads `a 2 + a 1 = 1`.
But `a 1 = 1` (the fixed point `0`) and `a 2 = 1` (the fixed point `21 = 25₈`), so the left-hand
side is `2`.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a165105.main) := by
  rintro ⟨-, h⟩
  have h2 := h 2
  revert h2
  decide +kernel
