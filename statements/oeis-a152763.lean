import Mathlib

/-!
# Comparing divisor counts of Catalan numbers near powers of two

Source: https://oeis.org/A152763.
Sequence authored by Omar E. Pol, December 14, 2008.
Conjecture by Jianing Song, June 16, 2022.
Source text: OEIS Foundation, CC BY-SA 4.0.
Credit: @unknownuser17769 for this formal statement.

A152763(n) is the number of positive divisors of the n-th Catalan number
A000108(n), with offset 0. We use Mathlib's Catalan sequence and finite set
of positive natural-number divisors directly.

This file selects the first explicitly stated conjecture in the entry:
for every k >= 3, A152763(2^k - 1) < A152763(2^k - 2).
The lower bound on k preserves the source's exact range and ensures that
both index subtractions are ordinary subtraction of nonnegative integers.
The entry's additional nonequality conjecture and suggested asymptotic
growth of the ratio are not part of this target.
-/

namespace OMA.S_oeis_a152763

/-- Number of positive divisors of the n-th Catalan number. -/
def a (n : ℕ) : ℕ :=
  (catalan n).divisors.card

/-- Song's divisor-count inequality near powers of two. -/
theorem main : ∀ k : ℕ, 3 ≤ k → a (2 ^ k - 1) < a (2 ^ k - 2) := by
  sorry

end OMA.S_oeis_a152763
