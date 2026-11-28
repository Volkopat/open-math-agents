import OMAStatements.S_oeis_a104863
import Mathlib

/-!
Credit: @ivillar
Disproof: computing the sequence (each step certified by Nat.eq_sqrt) gives a(13) = 358,
a(15) = 578 and a(17) = 935, while the conjectured recurrence would give a(17) = 578 + 358 + 1 = 937.
-/

namespace OMAA104863Helpers
open OMA.S_oeis_a104863

theorem step (k x y z : ℕ) (hx : a (k + 2) = x) (hy : a (k + 1) = y)
    (h1 : z * z ≤ x ^ 2 + y ^ 2) (h2 : x ^ 2 + y ^ 2 < (z + 1) * (z + 1)) : a (k + 3) = z := by
  show Nat.sqrt (a (k + 2) ^ 2 + a (k + 1) ^ 2) = z
  rw [hx, hy]
  exact (Nat.eq_sqrt.2 ⟨h1, h2⟩).symm

end OMAA104863Helpers

open OMA.S_oeis_a104863 OMAA104863Helpers in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a104863.main) := by
  intro h
  have h1 : a 1 = 10 := rfl
  have h2 : a 2 = 30 := rfl
  have h3 : a 3 = 31 := step 0 30 10 31 h2 h1 (by norm_num) (by norm_num)
  have h4 : a 4 = 43 := step 1 31 30 43 h3 h2 (by norm_num) (by norm_num)
  have h5 : a 5 = 53 := step 2 43 31 53 h4 h3 (by norm_num) (by norm_num)
  have h6 : a 6 = 68 := step 3 53 43 68 h5 h4 (by norm_num) (by norm_num)
  have h7 : a 7 = 86 := step 4 68 53 86 h6 h5 (by norm_num) (by norm_num)
  have h8 : a 8 = 109 := step 5 86 68 109 h7 h6 (by norm_num) (by norm_num)
  have h9 : a 9 = 138 := step 6 109 86 138 h8 h7 (by norm_num) (by norm_num)
  have h10 : a 10 = 175 := step 7 138 109 175 h9 h8 (by norm_num) (by norm_num)
  have h11 : a 11 = 222 := step 8 175 138 222 h10 h9 (by norm_num) (by norm_num)
  have h12 : a 12 = 282 := step 9 222 175 282 h11 h10 (by norm_num) (by norm_num)
  have h13 : a 13 = 358 := step 10 282 222 358 h12 h11 (by norm_num) (by norm_num)
  have h14 : a 14 = 455 := step 11 358 282 455 h13 h12 (by norm_num) (by norm_num)
  have h15 : a 15 = 578 := step 12 455 358 578 h14 h13 (by norm_num) (by norm_num)
  have h16 : a 16 = 735 := step 13 578 455 735 h15 h14 (by norm_num) (by norm_num)
  have h17 : a 17 = 935 := step 14 735 578 935 h16 h15 (by norm_num) (by norm_num)
  have := h 17 (by norm_num)
  rw [show 17 - 2 = 15 from rfl, show 17 - 4 = 13 from rfl, h17, h15, h13] at this
  norm_num at this
