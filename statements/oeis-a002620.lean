import Mathlib

/-!
# A002620: Quarter-squares: a(n) = floor(n/2)*ceiling(n/2). Equivalently, a(n) = floor(n^2/4).

Source: https://oeis.org/A002620
Credit: @mattdorman

The source states (an alternative form of Oppermann's conjecture): for `n > 2`, there is at least
one prime between `a(n)` and `a(n+1)`, where `a(n) = ⌊n²/4⌋`.

Reading used here: "between" is strict, `a(n) < p < a(n+1)`, as in Oppermann's conjecture.
`a(n) = n² / 4` with natural-number (floor) division.
-/

namespace OMA.S_oeis_a002620

/-- The quarter-squares `a(n) = ⌊n²/4⌋`. -/
def a (n : ℕ) : ℕ := n ^ 2 / 4

theorem main : ∀ n : ℕ, 2 < n → ∃ p : ℕ, p.Prime ∧ a n < p ∧ p < a (n + 1) := by
  sorry

end OMA.S_oeis_a002620
