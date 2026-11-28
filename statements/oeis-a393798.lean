import Mathlib

/-!
# A393798: Consecutive terms differ by a 3-smooth number

Source: https://oeis.org/A393798
Credit: @gblacher2
-/

namespace OMA.S_oeis_a393798

/-- The next term is prime and exceeds the previous one by a product of powers of 2 and 3. -/
def eligibleSuccessor (previous candidate : ℕ) : Prop :=
  candidate.Prime ∧ ∃ i j : ℕ, candidate = previous + 2 ^ i * 3 ^ j

/-- The greedy recurrence starting at 2 can be continued at every index. -/
theorem main :
    ∃ a : ℕ → ℕ, a 0 = 2 ∧
      ∀ n : ℕ, IsLeast {p : ℕ | eligibleSuccessor (a n) p} (a (n + 1)) := by
  sorry

end OMA.S_oeis_a393798
