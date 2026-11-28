import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A288599

Source: https://oeis.org/A288599
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The listed term a(4)=16, generating function and program give the recurrence from n=5. The formula printed with n>=4 would give 18 at n=4.
-/

namespace OMA.S_oeis_a288599

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 6
  | 3 => 10
  | 4 => 16
  | n+5 => 2 * reference (n+4) - reference (n+1)

def rewrite : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | false :: false :: w => [false, true, false, true] ++ rewrite w
  | true :: false :: w => [true, false, false, false] ++ rewrite w
  | false :: true :: w => false :: rewrite (true :: w)
  | true :: true :: w => true :: rewrite (true :: w)

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a288599
