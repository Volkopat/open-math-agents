import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A288317

Source: https://oeis.org/A288317
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The generating function, listed terms and program fix a(4)=22 and the recurrence from n=5. Applying the recurrence already at n=4 would give 23.
-/

namespace OMA.S_oeis_a288317

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 12
  | 4 => 22
  | n+5 => reference (n+4) + 3 * reference (n+3) - 2 * reference (n+2) - reference (n+1)

def rewrite : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | true :: w => [false, false] ++ rewrite w
  | false :: true :: w => false :: ([false, false] ++ rewrite w)
  | false :: false :: w => [false, false, false, true] ++ rewrite w

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a288317
