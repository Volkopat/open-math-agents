import OMAStatements.S_oeis_a121553
import Mathlib

-- Problem: A121553: Total area of all deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column.
-- Upstream: formal-conjectures statements/oeis-a121553.lean:0 (declaration OMA.S_oeis_a121553.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Using the defining formula four times, a(m+5), a(m+4), a(m+3), a(m+2) are expressed through
a(m+1) and (m+1)!. With C(k,2) = k (k-1) / 2 over the rationals, the recurrence becomes a
polynomial identity in m, a(m+1) and (m+1)!. -/

namespace A121553Aux

open OMA.S_oeis_a121553

theorem a_rec (n : ℕ) :
    a (n + 2) = ((n : ℤ) + 2) * a (n + 1) +
      ((n + 1).factorial : ℤ) * (1 + ((n + 2).choose 2 : ℤ)) := by
  rw [a]

theorem rec (m : ℕ) :
    a (m + 5) + (-2 * ((m : ℤ) + 5) - 3) * a (m + 4) +
      (((m : ℤ) + 5) ^ 2 + 4 * ((m : ℤ) + 5) - 3) * a (m + 3) +
      2 * (-((m : ℤ) + 5) ^ 2 + ((m : ℤ) + 5) + 3) * a (m + 2) +
      2 * (((m : ℤ) + 5) - 3) ^ 2 * a (m + 1) = 0 := by
  have h5 : a (m + 5) = (((m + 3 : ℕ) : ℤ) + 2) * a (m + 4) +
      ((m + 4).factorial : ℤ) * (1 + ((m + 5).choose 2 : ℤ)) := a_rec (m + 3)
  have h4 : a (m + 4) = (((m + 2 : ℕ) : ℤ) + 2) * a (m + 3) +
      ((m + 3).factorial : ℤ) * (1 + ((m + 4).choose 2 : ℤ)) := a_rec (m + 2)
  have h3 : a (m + 3) = (((m + 1 : ℕ) : ℤ) + 2) * a (m + 2) +
      ((m + 2).factorial : ℤ) * (1 + ((m + 3).choose 2 : ℤ)) := a_rec (m + 1)
  have h2 : a (m + 2) = ((m : ℤ) + 2) * a (m + 1) +
      ((m + 1).factorial : ℤ) * (1 + ((m + 2).choose 2 : ℤ)) := a_rec m
  have q5 : (a (m + 5) : ℚ) = ((m : ℚ) + 5) * (a (m + 4) : ℚ) +
      ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) *
        (1 + ((m : ℚ) + 5) * ((m : ℚ) + 4) / 2) := by
    rw [h5]
    push_cast [Nat.factorial_succ, Nat.cast_choose_two]
    ring
  have q4 : (a (m + 4) : ℚ) = ((m : ℚ) + 4) * (a (m + 3) : ℚ) +
      ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) *
        (1 + ((m : ℚ) + 4) * ((m : ℚ) + 3) / 2) := by
    rw [h4]
    push_cast [Nat.factorial_succ, Nat.cast_choose_two]
    ring
  have q3 : (a (m + 3) : ℚ) = ((m : ℚ) + 3) * (a (m + 2) : ℚ) +
      ((m : ℚ) + 2) * ((m + 1).factorial : ℚ) * (1 + ((m : ℚ) + 3) * ((m : ℚ) + 2) / 2) := by
    rw [h3]
    push_cast [Nat.factorial_succ, Nat.cast_choose_two]
    ring
  have q2 : (a (m + 2) : ℚ) = ((m : ℚ) + 2) * (a (m + 1) : ℚ) +
      ((m + 1).factorial : ℚ) * (1 + ((m : ℚ) + 2) * ((m : ℚ) + 1) / 2) := by
    rw [h2]
    push_cast [Nat.cast_choose_two]
    ring
  have key : ((a (m + 5) + (-2 * ((m : ℤ) + 5) - 3) * a (m + 4) +
      (((m : ℤ) + 5) ^ 2 + 4 * ((m : ℤ) + 5) - 3) * a (m + 3) +
      2 * (-((m : ℤ) + 5) ^ 2 + ((m : ℤ) + 5) + 3) * a (m + 2) +
      2 * (((m : ℤ) + 5) - 3) ^ 2 * a (m + 1) : ℤ) : ℚ) = 0 := by
    push_cast
    rw [q5, q4, q3, q2]
    ring
  exact_mod_cast key

end A121553Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a121553.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e1 : m + 5 - 1 = m + 4 := by omega
  have e2 : m + 5 - 2 = m + 3 := by omega
  have e3 : m + 5 - 3 = m + 2 := by omega
  have e4 : m + 5 - 4 = m + 1 := by omega
  rw [e1, e2, e3, e4]
  have h := A121553Aux.rec m
  push_cast
  exact h
