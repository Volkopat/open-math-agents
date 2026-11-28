import Mathlib

/-!
# A287614: Primes of the form (1 + x)^y + (-x)^y for some positive x, y.

Source: https://oeis.org/A287614
Credit: @agchua

Comment of A287614 (the entry is by Juri-Stepan Gerasimov, May 27 2017):
  Conjecture: If x is a positive number and (1 + x)^y + (-x)^y is an odd prime number, then y is
  other odd prime number or even power of two.
Reading: x and y are natural numbers, as in the name of the entry (positive x, y), and an even
power of two is a power 2^k with k >= 1: the entry's own examples 5 = 2^2 + (-1)^2 and
13 = 3^2 + (-2)^2 have y = 2. The claim is stated for every natural number y; for y = 0 the value
is 2, which is not odd.
-/

namespace OMA.S_oeis_a287614

/-- The value (1 + x)^y + (-x)^y, as an integer. -/
def f (x y : ℕ) : ℤ := (1 + (x : ℤ)) ^ y + (-(x : ℤ)) ^ y

/-- The conjecture: if x >= 1 and (1 + x)^y + (-x)^y is an odd prime p, then y is an odd prime
or y = 2^k for some k >= 1. -/
theorem main : ∀ x y p : ℕ, 1 ≤ x → f x y = (p : ℤ) → p.Prime → Odd p →
    (y.Prime ∧ Odd y) ∨ (∃ k : ℕ, 1 ≤ k ∧ y = 2 ^ k) := by
  sorry

end OMA.S_oeis_a287614
