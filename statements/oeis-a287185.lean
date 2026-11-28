import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A287185

Source: https://oeis.org/A287185
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The ordinary generating function, published terms and Mathematica program agree on lags 7 and 8 for the two negative terms. The displayed recurrence instead uses lags 6 and 7. The proof file checks its failure at n=8 as well.
-/

namespace OMA.S_oeis_a287185

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 14
  | 4 => 25
  | 5 => 47
  | 6 => 88
  | 7 => 166
  | n+8 => 3 * reference (n+6) + reference (n+5) + reference (n+3) - 3 * reference (n+1) - reference n

def rewrite : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | true :: w => [false, false] ++ rewrite w
  | false :: true :: w => false :: ([false, false] ++ rewrite w)
  | false :: false :: w => [false, false, true, false] ++ rewrite w

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a287185
