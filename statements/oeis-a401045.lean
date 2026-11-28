import Mathlib

/-!
# OEIS A401045

The entry asks whether infinitely many natural numbers have a square that
is the sum of two primes differing by six.
Source: https://oeis.org/A401045
Credit: @siddsg7
-/

namespace OMA.S_oeis_a401045

theorem main :
    {k : ℕ | ∃ p : ℕ, p.Prime ∧ (p + 6).Prime ∧ k ^ 2 = p + (p + 6)}.Infinite := by
  sorry

end OMA.S_oeis_a401045
