import OMAStatements.S_oeis_a123922
import Mathlib

open OMA.S_oeis_a123922

namespace P123922

theorem fsucc (m : ℕ) : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
  rw [Nat.factorial_succ]; push_cast; ring

theorem b_even (m : ℕ) : b (2 * m) =
    ((3 * m).factorial : ℚ) / ((m.factorial : ℚ) * ((2 * m).factorial : ℚ) * (2 * (m : ℚ) + 1)) := by
  rw [b, if_pos (by omega), show 2 * m / 2 = m by omega,
    Nat.cast_choose ℚ (by omega : m ≤ 3 * m), show 3 * m - m = 2 * m by omega]
  have f1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have f2 : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  have f3 : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
  field_simp

theorem b_odd (m : ℕ) : b (2 * m + 1) =
    ((3 * m + 1).factorial : ℚ) / (((m + 1).factorial : ℚ) * ((2 * m).factorial : ℚ) * (2 * (m : ℚ) + 1)) := by
  rw [b, if_neg (by omega), show (2 * m + 1) / 2 = m by omega,
    Nat.cast_choose ℚ (by omega : m + 1 ≤ 3 * m + 1), show 3 * m + 1 - (m + 1) = 2 * m by omega]
  have f1 : ((m + 1).factorial : ℚ) ≠ 0 := by positivity
  have f2 : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  have f3 : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
  field_simp

end P123922

open P123922 in
theorem OMA.solution : type_of% @OMA.S_oeis_a123922.main := by
  intro n hn
  have f1 : ∀ j : ℕ, ((3 * j).factorial : ℚ) ≠ 0 := fun j => by positivity
  have f2 : ∀ j : ℕ, ((2 * j).factorial : ℚ) ≠ 0 := fun j => by positivity
  have f3 : ∀ j : ℕ, ((j).factorial : ℚ) ≠ 0 := fun j => by positivity
  obtain ⟨j, rfl | rfl⟩ : ∃ j, n = 2 * j + 2 ∨ n = 2 * j + 3 := ⟨(n - 2) / 2, by omega⟩
  · simp only [a]
    rw [show 2 * j + 2 - 1 = 2 * j + 1 by omega, show 2 * j + 2 - 2 = 2 * j by omega,
      show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by ring, show 2 * j + 1 + 1 = 2 * (j + 1) by ring,
      b_even, b_odd, b_even, b_odd]
    rw [show 3 * (j + 1) + 1 = 3 * j + 1 + 1 + 1 + 1 by ring, show 3 * (j + 1) = 3 * j + 1 + 1 + 1 by ring,
      show 2 * (j + 1) = 2 * j + 1 + 1 by ring, show j + 1 + 1 = j + 2 by ring]
    rw [show j + 2 = j + 1 + 1 by ring]
    simp only [fsucc]
    have := f1 j; have := f2 j; have := f3 j
    push_cast
    field_simp
    ring
  · simp only [a]
    rw [show 2 * j + 3 - 1 = 2 * (j + 1) by omega, show 2 * j + 3 - 2 = 2 * j + 1 by omega,
      show 2 * j + 3 + 1 = 2 * (j + 2) by ring,
      show 2 * j + 1 + 1 = 2 * (j + 1) by ring,
      show 2 * j + 3 = 2 * (j + 1) + 1 by ring, b_even, b_odd, b_even, b_odd]
    rw [show 3 * (j + 2) = 3 * j + 1 + 1 + 1 + 1 + 1 + 1 by ring,
      show 3 * (j + 1) + 1 = 3 * j + 1 + 1 + 1 + 1 by ring, show 3 * (j + 1) = 3 * j + 1 + 1 + 1 by ring,
      show 2 * (j + 2) = 2 * j + 1 + 1 + 1 + 1 by ring,
      show 2 * (j + 1) = 2 * j + 1 + 1 by ring, show j + 1 + 1 = j + 2 by ring]
    rw [show j + 2 = j + 1 + 1 by ring]
    simp only [fsucc]
    have := f1 j; have := f2 j; have := f3 j
    push_cast
    field_simp
    ring
