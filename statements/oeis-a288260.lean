import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A288260

Source: https://oeis.org/A288260
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The two scanners implement the rules in the first and second conjectures separately. The same independently defined integer recurrence is used for both.
-/

namespace OMA.S_oeis_a288260

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | 3 => 16
  | n+4 => 2 * reference (n+3) + 2 * reference (n+1) - 3 * reference n

namespace RuleA

def rewrite : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | true :: w => [true, false, false] ++ rewrite w
  | false :: true :: w => false :: ([true, false, false] ++ rewrite w)
  | false :: false :: w => [false, false, true, false] ++ rewrite w

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

end RuleA

namespace RuleB

def rewrite : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | true :: w => [false, true, false] ++ rewrite w
  | false :: true :: w => false :: ([false, true, false] ++ rewrite w)
  | false :: false :: w => [false, true, false, true] ++ rewrite w

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

end RuleB

theorem main : ∀ n : ℕ, ((RuleA.word n).length : ℤ) = reference n ∧
    ((RuleB.word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a288260
