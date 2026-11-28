import OMAStatements.S_oeis_a207872
import Mathlib

/-!
# A207872: the denominator claim fails for `n = 2`

Take the digit list `bs = [false, true]` (low digit first).  It ends in `true`, has no two
adjacent `true`s, and its Fibonacci value is `0 · 1 + 1 · 2 = 2`.  But evaluating at one half gives
`0 + (1 + 0) / 2 = 1/2`, with denominator `2`, while the reversed binary value is `1`.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a207872.main) := by
  intro h
  have h2 := h 2 (by norm_num) [false, true] (by decide) (by decide) (by decide)
  revert h2
  decide +kernel
