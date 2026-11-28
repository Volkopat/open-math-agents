import OMAStatements.S_oeis_a243750
import Mathlib

/-!
# Disproof of the A243750 record conjecture at n = 998

998 > 103 and 998 = 2 (mod 3), but 998 is not a record index of A112801: the count for 995
is 41603 and the count for 998 is 41594. This is the failure recorded in OEIS A243750 by
Qiyuan Gu (Jul 24 2026). Both counts are evaluated by the kernel from the definition
(decide +kernel; no native code).
-/

namespace OMA.P_oeis_a243750

open OMA.S_oeis_a243750

lemma counts : count 998 < count 995 := by decide +kernel

end OMA.P_oeis_a243750

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a243750.main) := by
  intro h
  have h1 := (h 998 (by norm_num)).2 (by norm_num)
  have h2 := h1 995 (by norm_num) (by norm_num)
  have h3 := OMA.P_oeis_a243750.counts
  omega
