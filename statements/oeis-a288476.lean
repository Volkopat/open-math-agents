import Mathlib.Data.Nat.Basic

/-!
# Lengths of the literal iterates in A288476

Source: https://oeis.org/A288476
Credit: @blakestone-x

Iteration zero is 00. Replacements scan from left to right without overlap.
The signed recurrence is specified independently of the word.
-/

namespace OMA.S_oeis_a288476

def rewrite : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | true :: w => [false, true, true] ++ rewrite w
  | false :: true :: w => false :: ([false, true, true] ++ rewrite w)
  | false :: false :: w => [false, true, false, true] ++ rewrite w


def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | n+3 => 1 * reference (n+2) + 4 * reference (n+1) - 2 * reference n

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a288476
