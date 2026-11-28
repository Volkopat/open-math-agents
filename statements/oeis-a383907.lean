import Mathlib

/-!
# A383907: Echo primes: primes p such that the greatest prime factor of p-1 is a suffix of p

Source: https://oeis.org/A383907
Credit: @niclorusso

Conjecture (in the comments of A383907): There are infinitely many echo primes.

Conventions:
* For a prime p >= 3, the greatest prime factor of p - 1 is `(p - 1).primeFactors.max' _`, written
  here as `(p - 1).primeFactors.sup id` (p = 2 has p - 1 = 1 with no prime factor, and is not an
  echo prime: the value 0 is not a suffix of 2).
* "q is a suffix of p" means that the decimal expansion of p ends with that of q:
  p mod 10^L = q, where L is the number of decimal digits of q (`(Nat.digits 10 q).length`).
-/

namespace OMA.S_oeis_a383907

/-- The greatest prime factor of `n` (`0` if `n` has no prime factor). -/
def gpf (n : ℕ) : ℕ := n.primeFactors.sup id

/-- `p` is an echo prime: `p` is prime, `p - 1` has a prime factor, and the decimal expansion of
`p` ends with that of the greatest prime factor of `p - 1`. -/
def IsEcho (p : ℕ) : Prop :=
  p.Prime ∧ 0 < gpf (p - 1) ∧ p % 10 ^ (Nat.digits 10 (gpf (p - 1))).length = gpf (p - 1)

/-- The conjecture on A383907: there are infinitely many echo primes. -/
theorem main : {p : ℕ | IsEcho p}.Infinite := by
  sorry

end OMA.S_oeis_a383907
