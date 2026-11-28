import Mathlib.Data.Nat.Basic

/-!
# Lengths of the literal iterates in A287128

Source: https://oeis.org/A287128
Credit: @blakestone-x

Iteration zero is 00. Replacements scan from left to right without overlap.
The signed recurrence is specified independently of the word.
-/

namespace OMA.S_oeis_a287128

def rewrite : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | true :: w => [true, true, false] ++ rewrite w
  | false :: true :: w => false :: ([true, true, false] ++ rewrite w)
  | false :: false :: w => [false, false, true] ++ rewrite w


def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | 2 => 6
  | 3 => 13
  | 4 => 29
  | n+5 => 3 * reference (n+4) - 2 * reference (n+3) + 2 * reference (n+2) - 4 * reference (n+1) + 2 * reference n

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a287128
