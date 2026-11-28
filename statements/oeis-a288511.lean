import Mathlib.Data.Nat.Basic

/-!
# A288511 and the length of a binary replacement word

Source: https://oeis.org/A288511
Credit: @blakestone-x

Iteration zero is the word 00. Each match consumes two letters from the left.
An unmatched leading letter is copied. The numeric sequence is defined independently.

-/

namespace OMA.S_oeis_a288511

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, true, false, true] ++ rewrite w
  | true :: false :: w => [false, false, true] ++ rewrite w
  | false :: true :: w => false :: rewrite (true :: w)
  | true :: true :: w => true :: rewrite (true :: w)
termination_by w => w.length

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

def source : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 7
  | 4 => 9
  | 5 => 12
  | 6 => 17
  | 7 => 23
  | 8 => 33
  | 9 => 48
  | 10 => 70
  | 11 => 103
  | 12 => 152
  | 13 => 228
  | 14 => 343
  | 15 => 515
  | n+16 => 2*source (n+15) - source (n+14) + 2*source (n+13) -
      4*source (n+12) + 4*source (n+11) - 4*source (n+10) +
      4*source (n+9) - 4*source (n+8) + 4*source (n+7) -
      3*source (n+6) + 2*source (n+5) - 3*source (n+4) + 2*source (n+3)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = source n := by
  sorry

end OMA.S_oeis_a288511
