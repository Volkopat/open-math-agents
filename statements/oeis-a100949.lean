import Mathlib

/-!
# A100949: Number of partitions of n into a prime and a semiprime.

Source: https://oeis.org/A100949
Credit: @gblacher2

Conjecture (comment section of A100949):
"Marnell conjectures that a(n) > 0 for n > 10 after analyzing "many thousands of whole
numbers". I find no exceptions below 100 million." (Charles R Greathouse IV, May 04 2010),
citing Geoffrey R. Marnell, "Ten Prime Conjectures", Journal of Recreational Mathematics
33:3 (2004-2005), pp. 193-196.

The sequence has offset 1: 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 3, 2, 2, 1, ...

Modelling choices:
* A semiprime is a natural number with exactly two prime factors counted with multiplicity
  (`bigomega(n) == 2` in the PARI program of the entry), i.e. `ArithmeticFunction.cardFactors
  m = 2`; squares of primes such as 4 count, as in the example a(21) = #{7+2*7, 11+2*5, 17+2*2}.
* A partition of n into a prime and a semiprime is an unordered pair {p, s} with p prime,
  s semiprime and p + s = n. A prime is never a semiprime, so each such partition is determined
  by its prime part p, and `a n` counts the primes p < n such that n - p is a semiprime
  (this is the Haskell program of the entry: sum over semiprimes s < n of isprime(n - s)).
-/

namespace OMA.S_oeis_a100949

/-- `m` is a semiprime: it has exactly two prime factors, counted with multiplicity. -/
def IsSemiprime (m : ℕ) : Prop := ArithmeticFunction.cardFactors m = 2

instance : DecidablePred IsSemiprime := fun m => by
  unfold IsSemiprime; infer_instance

/-- A100949(n): the number of partitions of `n` into a prime and a semiprime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun p => p.Prime ∧ IsSemiprime (n - p)).card

/-- Marnell's conjecture: a(n) > 0 for n > 10. -/
theorem main : ∀ n : ℕ, 10 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a100949
