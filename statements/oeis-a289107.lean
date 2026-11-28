import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A289107

Source: https://oeis.org/A289107
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The displayed initial values are used before the integer recurrence begins. The literal word and the numeric reference are specified independently.
-/

namespace OMA.S_oeis_a289107

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 12
  | 4 => 22
  | n+5 => 2 * reference (n+4) - reference (n+2)

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, false, true, false] ++ rewrite w
  | false :: true :: w => [false, true, true] ++ rewrite w
  | true :: false :: w => [false, false, false] ++ rewrite w
  | true :: true :: w => true :: rewrite (true :: w)

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a289107
