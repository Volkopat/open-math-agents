import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A288600

Source: https://oeis.org/A288600
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The rule 10→1001 is the one in A288600 and its program. A288603 supplies the numeric sequence, whose generating function, data and program give a(3)=8 and the recurrence from n=4.
-/

namespace OMA.S_oeis_a288600

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 6
  | 3 => 8
  | n+4 => 2 * reference (n+3) - reference (n+1)

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, true, false, true] ++ rewrite w
  | true :: false :: w => [true, false, false, true] ++ rewrite w
  | false :: true :: w => false :: rewrite (true :: w)
  | true :: true :: w => true :: rewrite (true :: w)

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a288600
