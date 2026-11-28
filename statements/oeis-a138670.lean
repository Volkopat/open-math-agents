import Mathlib

/-!
# A138670: zero positions in Stewart's choral sequence

Source: https://oeis.org/A138670
Credit: @rgoldman73-dev

Sean A. Irvine's July 19, 2022 conjecture says these are "essentially partial
sums of A106036". With both entries indexed from zero, the precise reading is
a(0)=0 and a(n)=sum_{i=0}^{n-1} b(i), where b is A106036.

Stewart's choral sequence A116178 is the fixed point of 0->001, 1->011
starting with 0. A106036 is the fixed point of 1->12, 2->123, 3->1233
starting with 1. Both are defined below by their finite substitution iterates.
Each iterate is a prefix of the next. The (n+1)st Stewart iterate has at least
2^(n+1) zeros, and the (n+1)st gap iterate has at least 2^(n+1) letters.
Thus these finite prefixes contain the requested nth zero/letter; the default
in getD is never used. zeroPositions lists all zero positions in increasing
order, using zero-based indices. This fixes the offset ambiguity without
changing either sequence.

Sources for the defining substitutions: https://oeis.org/A116178 and
https://oeis.org/A106036.
-/

namespace OMA.S_oeis_a138670

def stewartLetter (x : ℕ) : List ℕ := if x = 0 then [0,0,1] else [0,1,1]

def stewartWord : ℕ → List ℕ
  | 0 => [0]
  | k+1 => (stewartWord k).flatMap stewartLetter

def gapLetter : ℕ → List ℕ
  | 1 => [1,2]
  | 2 => [1,2,3]
  | 3 => [1,2,3,3]
  | _ => []

def gapWord : ℕ → List ℕ
  | 0 => [1]
  | k+1 => (gapWord k).flatMap gapLetter

def zeroPositions : List ℕ → List ℕ
  | [] => []
  | x :: xs => (if x = 0 then [0] else []) ++ (zeroPositions xs).map Nat.succ

def a (n : ℕ) : ℕ := (zeroPositions (stewartWord (n+1))).getD n 0
def b (n : ℕ) : ℕ := (gapWord (n+1)).getD n 0

theorem main : ∀ n : ℕ, a n = ∑ i ∈ Finset.range n, b i := by
  sorry

end OMA.S_oeis_a138670
