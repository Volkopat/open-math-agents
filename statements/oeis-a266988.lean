import Mathlib

/-!
# A266988: The indices of primes for which the average of the primitive roots is < p/2.

Source: https://oeis.org/A266988
Credit: @agchua

Comment of A266988 (the entry is by Dimitri Papadopoulos, Jan 08 2016):
  These primes are all of the form p==3 (mod 4). (conjecture)
As in the entry's example and Mathematica program, the primitive roots of a prime p are the
g in 1..p-1 whose multiplicative order modulo p is p-1, and their average is their sum divided
by their number. The terms are the indices k with prime(k) having the property; the comment is
about the primes prime(k) themselves, so it is stated for every prime p: if the average of the
primitive roots of p is less than p/2, then p == 3 (mod 4).
-/

namespace OMA.S_oeis_a266988

/-- The primitive roots of p in 1..p-1: the g whose multiplicative order modulo p is p - 1. -/
noncomputable def primRoots (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (p - 1)).filter (fun g => orderOf (g : ZMod p) = p - 1)

/-- The average of the primitive roots of p. -/
noncomputable def avg (p : ℕ) : ℚ :=
  (∑ g ∈ primRoots p, (g : ℚ)) / (primRoots p).card

/-- The comment's conjecture: a prime p whose primitive roots have average < p/2 is 3 mod 4. -/
theorem main : ∀ p : ℕ, p.Prime → avg p < (p : ℚ) / 2 → p % 4 = 3 := by
  sorry

end OMA.S_oeis_a266988
