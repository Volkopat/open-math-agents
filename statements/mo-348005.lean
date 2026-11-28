import Mathlib

/-!
# A prime of the form (9n)! + n! + 1

Maximilian Janisch's MathOverflow question follows Peter's search for a prime
of this form. Peter specifies a positive integer n. At n = 0 the expression
would be 3, outside the search.

Sources: https://mathoverflow.net/questions/348005 and
https://math.stackexchange.com/questions/3450481
Credit: @witeg4
-/

namespace OMA.S_mo_348005

theorem main : ∃ n : ℕ, 0 < n ∧ ((9 * n).factorial + n.factorial + 1).Prime := by
  sorry

end OMA.S_mo_348005
