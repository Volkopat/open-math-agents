import Mathlib

/-!
# OEIS A374911

Bryle Morga conjectures that every positive integer occurs in this sequence.
The index starts at zero.

Source: https://oeis.org/A374911
-/

namespace OMA.S_oeis_a374911

/-- Each positive index refers back to two smaller indices given by modular powers. -/
def a (n : ℕ) : ℕ :=
  if _h : n = 0 then 1
  else a (2 ^ n % n) + a (3 ^ n % n)
termination_by n
decreasing_by all_goals exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

/-- Every positive integer occurs as a term of A374911. -/
theorem main : ∀ m : ℕ, 0 < m → ∃ n : ℕ, a n = m := by
  sorry

end OMA.S_oeis_a374911
