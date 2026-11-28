import OMAStatements.S_oeis_a265382
import Mathlib

namespace A265382Aux

open OMA.S_oeis_a265382 in
lemma a1 : a 1 = 4 := by decide

open OMA.S_oeis_a265382 in
lemma a2 : a 2 = 8 := by decide

open OMA.S_oeis_a265382 in
lemma a3 : a 3 = 13 := by decide

open OMA.S_oeis_a265382 in
lemma a4 : a 4 = 20 := by decide

open OMA.S_oeis_a265382 in
lemma a5 : a 5 = 27 := by decide

end A265382Aux

open OMA.S_oeis_a265382 A265382Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a265382.main) := by
  intro h
  have h5 := h.2.2.2.1 5 (by norm_num)
  rw [show (5 : ℕ) - 1 = 4 from rfl, show (5 : ℕ) - 2 = 3 from rfl,
    show (5 : ℕ) - 3 = 2 from rfl, show (5 : ℕ) - 4 = 1 from rfl, a5, a4, a3, a2, a1] at h5
  norm_num at h5
