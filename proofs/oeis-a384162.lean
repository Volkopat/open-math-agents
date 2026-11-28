import OMAStatements.S_oeis_a384162
import Mathlib

/-!
# OEIS A384162: the stated identity fails at `n = 2`

Over a two-letter alphabet the words of length `2` are `00, 01, 10, 11`. Their run-length
products are `2, 1, 1, 2`, so `markedWords 2 = 6`.

On the other side `companion 1 = U(4)` at index `1`, i.e. `4`, so `2 · companion 1 = 8 ≠ 6`.
-/

open OMA.S_oeis_a384162

namespace OMA.A384162

lemma markedWords_two : markedWords 2 = 6 := by decide

lemma companion_one : companion 1 = 4 := by decide

end OMA.A384162

open OMA.A384162 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a384162.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  rw [markedWords_two, show (2 : ℕ) - 1 = 1 from rfl, companion_one] at h2
  norm_num at h2
