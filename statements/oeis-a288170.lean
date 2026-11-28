import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A288170

Source: https://oeis.org/A288170
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The ordinary generating function, closed form, Mathematica program and published terms use coefficient -3 at lag 3. The displayed recurrence has -4. The companion proof also checks the discrepancy at n=6.
-/

namespace OMA.S_oeis_a288170

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | 3 => 16
  | 4 => 34
  | n+5 => 3 * reference (n+4) - reference (n+3) - 3 * reference (n+2) + 2 * reference (n+1)

def rewrite : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | true :: w => [false, false, false] ++ rewrite w
  | false :: true :: w => false :: ([false, false, false] ++ rewrite w)
  | false :: false :: w => [false, false, true, false] ++ rewrite w

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a288170
