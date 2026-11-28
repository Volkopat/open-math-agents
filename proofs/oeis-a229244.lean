import OMAStatements.S_oeis_a229244
import Mathlib

open OMA.S_oeis_a229244

namespace P229244

theorem fsucc (m : ℕ) : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
  rw [Nat.factorial_succ]; push_cast; ring

theorem a_odd (m : ℕ) : a (2 * m + 1) = ((2 * m + 1).factorial : ℚ) / ((m : ℚ) + 1) := by
  rw [a, if_pos (by omega), show (2 * m + 1) / 2 = m by omega,
    Nat.cast_choose ℚ (by omega : m + 1 ≤ 2 * m + 1), show 2 * m + 1 - (m + 1) = m by omega, fsucc m]
  have f1 : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem a_even (m : ℕ) : a (2 * m + 2) =
    ((2 * m + 2).factorial : ℚ) * (2 * (m : ℚ) + 1) / (2 * ((m : ℚ) + 1) ^ 2) := by
  rw [a, if_neg (by omega), show (2 * m + 2) / 2 = m + 1 by omega, show m + 1 - 1 = m by omega,
    Nat.cast_choose ℚ (by omega : m + 1 ≤ 2 * m + 2), show 2 * m + 2 - (m + 1) = m + 1 by omega, fsucc m]
  have f1 : (m.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end P229244

open P229244 in
theorem OMA.solution : type_of% @OMA.S_oeis_a229244.main := by
  intro n hn
  obtain ⟨j, rfl | rfl⟩ : ∃ j, n = 2 * j + 4 ∨ n = 2 * j + 5 := ⟨(n - 4) / 2, by omega⟩
  · rw [show 2 * j + 4 - 1 = 2 * (j + 1) + 1 by omega, show 2 * j + 4 - 2 = 2 * j + 2 by omega,
      show 2 * j + 4 - 3 = 2 * j + 1 by omega, show 2 * j + 4 = 2 * (j + 1) + 2 by ring,
      a_odd, a_even, a_even, a_odd]
    rw [show 2 * (j + 1) + 2 = 2 * j + 1 + 1 + 1 + 1 by ring, show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring,
      show 2 * j + 2 = 2 * j + 1 + 1 by ring, fsucc, fsucc, fsucc]
    have f1 : ((2 * j + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · rw [show 2 * j + 5 - 1 = 2 * (j + 1) + 2 by omega, show 2 * j + 5 - 2 = 2 * (j + 1) + 1 by omega,
      show 2 * j + 5 - 3 = 2 * j + 2 by omega, show 2 * j + 5 = 2 * (j + 2) + 1 by ring,
      a_odd, a_even, a_odd, a_even]
    rw [show 2 * (j + 2) + 1 = 2 * j + 1 + 1 + 1 + 1 + 1 by ring,
      show 2 * (j + 1) + 2 = 2 * j + 1 + 1 + 1 + 1 by ring, show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring,
      show 2 * j + 2 = 2 * j + 1 + 1 by ring, fsucc, fsucc, fsucc, fsucc]
    have f1 : ((2 * j + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
