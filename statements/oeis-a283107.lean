import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# A283107: Numbers k such that tau(4*(k - 1)) is prime.

Source: https://oeis.org/A283107

The entry's conjecture (comment by Charles R Greathouse IV, confirmed in the
next comment) is that A283107 is a supersequence of A281312, the numbers n
such that sigma(4*(n-1)) is prime. Both sequences are lists of positive
integers defined by a membership test, so the supersequence claim is the
implication between the two tests.

Here `sigma 1` is the sum of divisors (sigma) and `sigma 0` the number of
divisors (tau). The test needs 4*(k-1) to be positive, hence `2 ≤ k`.
-/

namespace OMA.S_oeis_a283107

open ArithmeticFunction

theorem main : ∀ k : ℕ, 2 ≤ k →
    Nat.Prime (sigma 1 (4 * (k - 1))) → Nat.Prime (sigma 0 (4 * (k - 1))) := by
  sorry

end OMA.S_oeis_a283107
