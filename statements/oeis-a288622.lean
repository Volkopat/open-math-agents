import Mathlib

/-!
The A288622 mapping replaces 00 by 0110 and 1 by 01. Starting at the first
iterate, the words consist of blocks 1, 01, 001 followed by a final zero.
Sources: https://oeis.org/A288622 and https://oeis.org/A288465
-/

namespace OMA.S_oeis_a288622

def scan : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | false :: false :: w => [false, true, true, false] ++ scan w
  | false :: true :: w => [false, false, true] ++ scan w
  | true :: w => [false, true] ++ scan w

def word : ℕ → List Bool
  | 0 => [false, false]
  | n + 1 => scan (word n)

def a288465 : ℕ → ℕ
  | 0 => 2
  | 1 => 4
  | 2 => 6
  | 3 => 10
  | n + 4 => 2 * a288465 (n + 3) - a288465 n

theorem main : ∀ n : ℕ, (word n).length = a288465 n := by
  sorry

end OMA.S_oeis_a288622
