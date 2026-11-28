import Mathlib

/-!
# A071011: Numbers n such that n is a sum of 2 squares (i.e., n is in A001481(k)) and sigma(n) == 0 (mod 4).

Source: https://oeis.org/A071011
Credit: @ShoQo

It is conjectured that if m is not a sum of 2 squares (i.e., m is in A022544(k))
sigma(m) == 0 (mod 4).

Formalization notes:
* "Sum of 2 squares" (A001481) allows zero squares, as in the OEIS entry (A001481 starts
  0, 1, 2, 4, 5, 8, 9, ...), so A022544 is its complement.
* `sigma` is the sum of divisors, `ArithmeticFunction.sigma 1`.
-/

namespace OMA.S_oeis_a071011

theorem main :
    ∀ m : ℕ, (¬ ∃ x y : ℕ, m = x ^ 2 + y ^ 2) → ArithmeticFunction.sigma 1 m % 4 = 0 := by
  sorry

end OMA.S_oeis_a071011
