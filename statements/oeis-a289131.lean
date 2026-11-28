import Mathlib.Data.Nat.Basic

/-!
# A289131 and the length of a binary replacement word

Source: https://oeis.org/A289131
Credit: @blakestone-x

Iteration zero is the word 00. Each match consumes two letters from the left.
An unmatched leading letter is copied. The numeric sequence is defined independently.

-/

namespace OMA.S_oeis_a289131

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, false, true, false] ++ rewrite w
  | false :: true :: w => [false, true, true] ++ rewrite w
  | true :: false :: w => [false, true, false] ++ rewrite w
  | true :: true :: w => true :: rewrite (true :: w)
termination_by w => w.length

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 18
  | 5 => 28
  | n+6 => reference (n+5) + 3*reference (n+4) - 3*reference (n+3) -
      2*reference (n+2) + 2*reference (n+1)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a289131
