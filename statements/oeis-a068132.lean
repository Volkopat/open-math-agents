import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Triangular numbers with a prescribed triangular digit sum

Source: https://oeis.org/A068132
Credit: @jatin6

Amarnath Murthy's 2002 entry conjectures infinitude for every triangular
target. Infinitude of a set of natural numbers is expressed by unboundedness.
-/

namespace OMA.S_oeis_a068132

def tri (n : ℕ) : ℕ := n * (n + 1) / 2

def digitSum (x : ℕ) : ℕ := (Nat.digits 10 x).sum

theorem main : ∀ t B : ℕ, ∃ n : ℕ, B < tri n ∧ digitSum (tri n) = tri t := by
  sorry

end OMA.S_oeis_a068132
