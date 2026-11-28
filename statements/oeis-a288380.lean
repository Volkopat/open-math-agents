import Mathlib

/-!
# Lengths of the words in OEIS A288380

Clark Kimberling conjectured that the integer sequence below counts the letters in
the successive words of OEIS A288377. A pass scans the old word from left to right
and replaces disjoint occurrences. It copies an unmatched zero. The initial word
has index zero. The five given values determine the recurrence from index five.

Sources: https://oeis.org/A288380 and https://oeis.org/A288377.
Formalization: @Liungang, with OpenAI Codex.
-/

namespace OMA.S_oeis_a288380

/-- One pass of the substitution, using false for zero and true for one. -/
def rewriteWord : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | false :: false :: xs => false :: false :: false :: true :: rewriteWord xs
  | false :: true :: xs => false :: true :: false :: rewriteWord xs
  | true :: xs => true :: false :: rewriteWord xs

/-- The word after n passes, starting from 00. -/
def word (n : ℕ) : List Bool := (rewriteWord^[n]) [false, false]

/-- The independently specified integer sequence A288380. -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 7
  | 3 => 11
  | 4 => 20
  | n + 5 => 3 * a (n + 4) - 3 * a (n + 3) + 3 * a (n + 2) - 3 * a (n + 1) + a n

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = a n := by
  sorry

end OMA.S_oeis_a288380
