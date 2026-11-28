import Mathlib

/-!
# MathOverflow 366772: A question related to the Hofstadter–Conway \$10000 sequence

Source: https://mathoverflow.net/questions/366772
Credit: @AngelHS12

The Hofstadter–Conway \$10000 sequence (OEIS A004001) is `c(1) = c(2) = 1` and
`c(n) = c(c(n-1)) + c(n - c(n-1))` for `n ≥ 3`. The question's variant (OEIS A287422) is
`c*(1) = c*(2) = 1` and `c*(n) = n - c*(c*(n-1)) - c*(n - c*(n-1))` for `n ≥ 3`.

Conjecture (stated in the question, checked there up to `2^32`):
`c(n) - n/2 ≥ |c*(n) - n/2|` for all `n ≥ 1`.

Conventions:
* Both sequences are indexed from 1, as in the source; the value at index `0` is an unused placeholder.
* The recursive calls are written with `min (·) (n - 1)` and `max (·) 1` only so that Lean accepts the
  definitions as terminating: for the actual sequences `1 ≤ c(n-1) ≤ n-1` and `1 ≤ c*(n-1) ≤ n-1`, so these
  clamps never change a value, and the definitions agree with the recurrences above.
-/

namespace OMA.S_mo_366772

/-- The Hofstadter–Conway \$10000 sequence `c` (OEIS A004001). -/
def c : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => c (min (c (n + 2)) (n + 2)) + c (n + 3 - max (c (n + 2)) 1)
decreasing_by all_goals omega

/-- The variant `c*` of the question (OEIS A287422). -/
def cStar : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => n + 3 - cStar (min (cStar (n + 2)) (n + 2)) - cStar (n + 3 - max (cStar (n + 2)) 1)
decreasing_by all_goals omega

/-- The conjecture of MathOverflow 366772. -/
theorem main : ∀ n : ℕ, 1 ≤ n → |(cStar n : ℝ) - n / 2| ≤ (c n : ℝ) - n / 2 := by
  sorry

end OMA.S_mo_366772
