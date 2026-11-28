import Mathlib.Data.Nat.Basic

/-!
# A288668 and the length of a binary replacement word

Source: https://oeis.org/A288668
Credit: @blakestone-x

Iteration zero is the word 00. Each match consumes two letters from the left.
An unmatched leading letter is copied. The numeric sequence is defined independently.
The displayed terms and generating function fix initial values 2, 4, 5 at indices 0, 1, 2.
-/

namespace OMA.S_oeis_a288668

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, true, true, false] ++ rewrite w
  | true :: false :: w => [false, false, false] ++ rewrite w
  | b :: true :: w => b :: rewrite (true :: w)
termination_by w => w.length

def word : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => rewrite (word n)

def reference : ℕ → ℕ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | n + 3 => reference (n+1) + 2*reference n

theorem main : ∀ n : ℕ, (word n).length = reference n := by
  sorry

end OMA.S_oeis_a288668
