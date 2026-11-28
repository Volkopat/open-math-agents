import Mathlib.Data.Nat.Basic

/-!
# A288523 and the length of a binary replacement word

Source: https://oeis.org/A288523
Credit: @blakestone-x

Iteration zero is the word 00. Each match consumes two letters from the left.
An unmatched leading letter is copied. The numeric sequence is defined independently.

-/

namespace OMA.S_oeis_a288523

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, true, false, true] ++ rewrite w
  | true :: false :: w => [false, true, false] ++ rewrite w
  | b :: true :: w => b :: rewrite (true :: w)
termination_by w => w.length

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 8
  | 4 => 11
  | n+5 => reference (n+4) + reference (n+3) + reference (n+2) -
      2*reference (n+1)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a288523
