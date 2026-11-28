import OMAStatements.S_oeis_a027088
import Mathlib

namespace OMA.P027088

open OMA.S_oeis_a027088

lemma v1 : a 1 = 1 := by decide

lemma v2 : a 2 = 3 := by decide

lemma v3 : a 3 = 6 := by decide

lemma v4 : a 4 = 16 := by decide

lemma v5 : a 5 = 41 := by decide

lemma v6 : a 6 = 107 := by decide

lemma v7 : a 7 = 283 := by decide

end OMA.P027088

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a027088.main) := by
  intro h
  have h7 := h 7 (by norm_num)
  norm_num [OMA.P027088.v1, OMA.P027088.v2, OMA.P027088.v3, OMA.P027088.v4, OMA.P027088.v5,
    OMA.P027088.v6, OMA.P027088.v7] at h7
