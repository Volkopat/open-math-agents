import OMAStatements.S_oeis_a327136
import Mathlib

-- Shorter disproof of OEIS A327136: at n = 0 the bounds force 1 < term 0 < 2. This version: @tylerpixel

open OMA.S_oeis_a327136 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a327136.main) := by
  intro h
  obtain ⟨a, b⟩ := h 0
  obtain c | c : term 0 ≤ 1 ∨ 2 ≤ term 0 := by omega
  all_goals rify at c; norm_num at a b; linarith [Real.pi_gt_three, Real.pi_lt_d4]
