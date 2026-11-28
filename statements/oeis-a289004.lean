import Mathlib.Data.Nat.Basic

/-!
# A289004 and the length of a binary replacement word

Source: https://oeis.org/A289004
Credit: @blakestone-x

Iteration zero is the word 00. Each match consumes two letters from the left.
An unmatched leading letter is copied. The numeric sequence is defined independently.
The displayed terms fix a(8)=151 and a(9)=257.
-/

namespace OMA.S_oeis_a289004

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, false, true, false] ++ rewrite w
  | false :: true :: w => [false, false, true] ++ rewrite w
  | true :: false :: w => [false, true, false] ++ rewrite w
  | true :: true :: w => true :: rewrite (true :: w)

def word : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => rewrite (word n)

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 18
  | 5 => 31
  | 6 => 52
  | 7 => 89
  | 8 => 151
  | 9 => 257
  | n+10 => 2 * reference (n+9) - reference (n+8) + 2 * reference (n+6) -
      reference (n+5) + reference (n+3) - reference (n+2) - reference n

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a289004
