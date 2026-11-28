import Mathlib

/-!
# The `5n + 1` sequence starting at 7

Source: https://mathoverflow.net/questions/462321/5n1-sequence-starting-at-7
Credit: @shc261392

Consider the variant of the Collatz function `f(n) = n / 2` for even `n` and `f(n) = 5n + 1` for
odd `n`. Question: can one prove that the orbit of `7` diverges to infinity?

Reading used here (the affirmative answer): the iterates `f^[k] 7` tend to infinity.
-/

namespace OMA.S_mo_462321

/-- The `5n + 1` map. -/
def f (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 5 * n + 1

theorem main : Filter.Tendsto (fun k : ℕ => f^[k] 7) Filter.atTop Filter.atTop := by
  sorry

end OMA.S_mo_462321
