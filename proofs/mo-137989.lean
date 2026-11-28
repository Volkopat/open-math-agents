import OMAStatements.S_mo_137989
import Mathlib

/-!
# MathOverflow 137989: the congruence modulo `p³` fails for `p = 3`, `n = 1`

With the trinomial-weighted definition, `apery 2 = 721` and `apery 0 = 1`, and
`721 - 1 = 720 = 26 · 27 + 18` is not divisible by `27`.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_137989.main) := by
  intro h
  have h3 := h 3 1 (by norm_num) (by norm_num)
  revert h3
  decide +kernel
