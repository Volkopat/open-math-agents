import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A285665

Source: https://oeis.org/A285665
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The displayed term a(7)=90 is included; the stated recurrence then applies for n>7.
-/

namespace OMA.S_oeis_a285665

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | 2 => 6
  | 3 => 10
  | 4 => 17
  | 5 => 29
  | 6 => 51
  | 7 => 90
  | n+8 => reference (n+7) + 2 * reference (n+6) - reference (n+5) - reference (n+4) + 2 * reference (n+3) - 2 * reference (n+1)

def rewrite : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | true :: w => [false, false, false] ++ rewrite w
  | false :: true :: w => false :: ([false, false, false] ++ rewrite w)
  | false :: false :: w => [false, false, true] ++ rewrite w

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a285665
