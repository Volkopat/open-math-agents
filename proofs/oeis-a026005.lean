import OMAStatements.S_oeis_a026005
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a026005.main := by
  intro k
  simp only [OMA.S_oeis_a026005.a, show 4 * (k + 2) + 1 = 4 * k + 9 by ring,
    show 4 * (k + 1) + 1 = 4 * k + 5 by ring,
    Nat.cast_choose ℚ (show k + 2 ≤ 4 * k + 9 by omega),
    Nat.cast_choose ℚ (show k + 1 ≤ 4 * k + 5 by omega),
    Nat.cast_choose ℚ (show k ≤ 4 * k + 1 by omega),
    show 4 * k + 9 - (k + 2) = 3 * k + 7 by omega, show 4 * k + 5 - (k + 1) = 3 * k + 4 by omega,
    show 4 * k + 1 - k = 3 * k + 1 by omega, Nat.factorial_succ]
  push_cast
  field_simp
  ring
