import OMAStatements.S_oeis_a073503
import Mathlib

-- The second conjecture fails at n = 46: the 46th term of A073503 is 102 (OEIS data 5, 10, ..., 100, 101,
-- 102), and |102 - 92| = 10 is not below sqrt 46 < 7 (Greathouse, OEIS A073503: the conjectures are refuted).

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a073503.main) := by
  intro h
  have hq : OMA.S_oeis_a073503.qualifies 102 := by decide +kernel
  have hc : Nat.count OMA.S_oeis_a073503.qualifies 102 = 45 := by decide +kernel
  have h46 : OMA.S_oeis_a073503.a 46 = 102 := by
    unfold OMA.S_oeis_a073503.a
    rw [show 46 - 1 = 45 from rfl, ← hc]
    exact Nat.nth_count hq
  have hb := h.2 46 (by norm_num)
  rw [h46] at hb
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 46 by norm_num)
  have hs0 := Real.sqrt_nonneg 46
  push_cast at hb
  rw [show ((102 : ℝ) - 2 * 46) = 10 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 10)] at hb
  nlinarith
