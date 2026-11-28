import Mathlib.Data.Nat.Basic

/-!
# Binary replacement lengths in A288429

Source: https://oeis.org/A288429
Credit: @blakestone-x

Each pass reads the old word from left to right, consuming nonoverlapping matches.
The conjecture printed in A288429 replaces the single letter 1 by 100. Its cited companion A288426 instead replaces the pair 10 by 100. The statement follows the printed conjecture. The proof file separately proves the companion rule at every index.
-/

namespace OMA.S_oeis_a288429

def reference : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | n+4 => 2 * reference (n+3) - reference (n+2) + reference (n+1) - reference n

def rewrite : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | true :: w => [true, false, false] ++ rewrite w
  | false :: true :: w => false :: ([true, false, false] ++ rewrite w)
  | false :: false :: w => [false, true, false, true] ++ rewrite w

def word : ℕ → List Bool
  | 0 => [false, false]
  | n+1 => rewrite (word n)

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = reference n := by
  sorry

end OMA.S_oeis_a288429
