import OMAStatements.S_oeis_a383456
import Mathlib

open OMA.S_oeis_a383456

theorem OMA.solution : type_of% @OMA.S_oeis_a383456.main := by
  intro n
  show hyperCoeff (n + 1) 1 - hyperCoeff (n + 1 + 1) 0 = _
  unfold hyperCoeff
  rw [Nat.cast_choose ℚ (show n ≤ 2 * n + 4 by omega), show 2 * n + 4 - n = n + 4 by omega]
  rw [show 2 * (n + 1) + 3 * 1 = (2 * n + 4) + 1 by ring, show 2 * (n + 1 + 1) + 3 * 0 = 2 * n + 4 by ring,
    show 1 + (n + 1) + 2 * 1 = (n + 3) + 1 by ring, show 1 + (n + 1 + 1) + 2 * 0 = n + 3 by ring,
    show n + 4 = (n + 3) + 1 by ring, show n + 1 + 1 = (n + 1) + 1 by ring]
  simp only [Nat.factorial_succ, Nat.factorial_one, Nat.factorial_zero]
  push_cast
  have h1 : ((2 * n + 4).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((n + 3).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring
