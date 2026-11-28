import Mathlib

/-!
# A285666: iterate lengths of the map 00 → 001, 1 → 010, starting with 00.

Source: https://oeis.org/A285666 and https://oeis.org/A001580.
Credit: @jaredwilder (ChatGPT).

The source uses Mathematica StringReplace with disjoint left-to-right matches,
starting at w[0] = 00. Unmatched zeroes are copied. Its length conjecture
compares positive iterate indices n with A001580(n) = 2^n + n^2
(the source's Table[StringLength[w[n]], {n, 1, 35}] starts at 1).
-/

namespace OMA.S_oeis_a285666

def scan : List Bool → List Bool
  | false :: false :: xs => [false,false,true] ++ scan xs
  | true :: xs => [false,true,false] ++ scan xs
  | x :: xs => x :: scan xs
  | [] => []

def word : ℕ → List Bool
  | 0 => [false,false]
  | n+1 => scan (word n)

theorem main : ∀ n : ℕ, 1 ≤ n → (word n).length = 2^n + n^2 := by
  sorry

end OMA.S_oeis_a285666
