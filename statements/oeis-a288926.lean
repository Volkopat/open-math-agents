import Mathlib

/-!
# The conjecture on iterate lengths in OEIS A288926

Each pass replaces `00` by `1000` and `10` by `0001`, starting with the
word `00` at index zero. The conjecture states that the length of the word
after each pass agrees with the corresponding term of A288925, including
the initial word at index zero.

Sources: https://oeis.org/A288926 and https://oeis.org/A288925
Credit: @lenpr
-/

namespace OMA.S_oeis_a288926

/-- One left-to-right, nonoverlapping replacement pass, with false for 0 and
true for 1. A match consumes two input bits; an unmatched bit is copied. -/
def rewriteWord : List Bool → List Bool
  | false :: false :: rest => [true, false, false, false] ++ rewriteWord rest
  | true :: false :: rest => [false, false, false, true] ++ rewriteWord rest
  | bit :: rest => bit :: rewriteWord rest
  | [] => []

def word : Nat → List Bool
  | 0 => [false, false]
  | n + 1 => rewriteWord (word n)

/-- The five initial terms and the integer recurrence defining A288925. -/
def predicted : Nat → Int
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | 3 => 13
  | 4 => 26
  | n + 5 => predicted (n + 4) + predicted (n + 3) +
      3 * predicted (n + 1) - 2 * predicted n

theorem main : ∀ n : Nat, ((word n).length : Int) = predicted n := by
  sorry

end OMA.S_oeis_a288926
