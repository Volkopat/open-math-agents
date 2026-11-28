import Mathlib.Data.Nat.Basic

/-!
# Lengths of the literal iterates in A287381

Source: https://oeis.org/A287381
Credit: @blakestone-x

Iteration zero is 00. Replacements scan from left to right without overlap.
The signed recurrence is specified independently of the word.
-/

namespace OMA.S_oeis_a287381

def rewrite : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | true :: w => [true, false] ++ rewrite w
  | false :: true :: w => false :: ([true, false] ++ rewrite w)
  | false :: false :: w => [false, false, true, false] ++ rewrite w


def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | n+3 => 1 * reference (n+2) + 2 * reference (n+1) - 1 * reference n

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a287381
