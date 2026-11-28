import Mathlib

/-!
# A247077: Composite numbers for which the harmonic mean of proper divisors is an integer.

Source: https://oeis.org/A247077
Credit: @Pampasgras

The OEIS conjecture (Chai Wah Wu, Dec 15 2020): all terms are of the form m*(sigma(m)-1) where
sigma(m)-1 is prime.

Translation notes.
* The proper divisors of k are the divisors d of k with d < k (`Nat.properDivisors`). Their harmonic
  mean is their number divided by the sum of their reciprocals, computed in ℚ (`properHarmonicMean`).
  The %e example: the proper divisors of 1645 have harmonic mean 5.
* A term is a composite number k, that is 1 < k and k is not prime, whose proper-divisor harmonic
  mean is an integer. With these definitions the composites k ≤ 6000 that qualify are exactly 1645,
  and 88473 qualifies, matching the %S data; the definition also agrees with the equivalent criterion
  in the OEIS comments (sigma(k) - 1 divides k*(tau(k) - 1)) for every composite k ≤ 6000.
* sigma(m) is `ArithmeticFunction.sigma 1 m`, the sum of the divisors of m. The subtraction is in ℕ;
  it never matters, since for m = 0 the value sigma(0) - 1 = 0 is not prime, and for m ≥ 1 we have
  sigma(m) ≥ 1. No range is put on m: the conjecture names none.
* Checked numerically: all three known terms (1645, 88473, 63626653506) have this form, with
  m = 35, 231 and 171366.
-/

namespace OMA.S_oeis_a247077

/-- The harmonic mean of the proper divisors of `k`: their number divided by the sum of their
reciprocals. -/
def properHarmonicMean (k : ℕ) : ℚ :=
  (k.properDivisors.card : ℚ) / ∑ d ∈ k.properDivisors, (d : ℚ)⁻¹

/-- Every composite number whose proper divisors have an integer harmonic mean is of the form
m * (sigma(m) - 1) with sigma(m) - 1 prime. -/
theorem main :
    ∀ k : ℕ, 1 < k → ¬ k.Prime → (∃ z : ℤ, properHarmonicMean k = z) →
      ∃ m : ℕ, (ArithmeticFunction.sigma 1 m - 1).Prime ∧
        k = m * (ArithmeticFunction.sigma 1 m - 1) := by
  sorry

end OMA.S_oeis_a247077
