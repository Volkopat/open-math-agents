import Mathlib.Data.Nat.Basic

/-!
# Lengths of the literal iterates in A289060

Source: https://oeis.org/A289060
Credit: @blakestone-x

Iteration zero is 00. Replacements scan from left to right without overlap.
The signed recurrence is specified independently of the word.
-/

namespace OMA.S_oeis_a289060

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false,false,true,false] ++ rewrite w
  | false :: true :: w => [false,true,false] ++ rewrite w
  | true :: false :: w => [false,true,true] ++ rewrite w
  | true :: true :: w => true :: rewrite (true :: w)

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 17
  | 5 => 25
  | 6 => 36
  | 7 => 51
  | n+8 => 3 * reference (n+7) - 3 * reference (n+6) + reference (n+5)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a289060
