import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A287439

Source: https://oeis.org/A287439
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The data and generating function give a(0)=2, a(1)=4, a(2)=7, correcting shifted initial subscripts in the prose.
-/

namespace OMA.S_oeis_a287439

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | n+3 => 2 * reference (n+1) + 2 * reference n

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [true, false, false, false] ++ rewrite w
  | true :: false :: w => [false, false, false] ++ rewrite w
  | false :: true :: w => false :: rewrite (true :: w)
  | true :: true :: w => true :: rewrite (true :: w)

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a287439
