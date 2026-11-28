import Mathlib

/-!
# A094383: Primes p such that d>0 exists and p-d, p-2*d and p-3*d are also primes.

Source: https://oeis.org/A094383
Credit: @divmxnd0x

Conjecture (Alex Ratushnyak, Sep 08 2012, stated in A094383): only 25 primes are not in the
sequence, namely 2, 3, 5, 7, 11, 13, 17, 19, 31, 37, 47, 61, 67, 71, 73, 89, 109, 137, 179, 211,
277, 337, 379, 499, 557.

Formalization notes:
* `p` is a term when `p` is prime and there is `d > 0` with `p - d`, `p - 2d`, `p - 3d` all prime
  (`3d < p`, so that the subtractions are exact).
* The conjecture: the primes that are not terms are exactly the 25 listed ones.
-/

namespace OMA.S_oeis_a094383

/-- `p` is a term of A094383. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ ∃ d : ℕ, 0 < d ∧ 3 * d < p ∧ (p - d).Prime ∧ (p - 2 * d).Prime ∧ (p - 3 * d).Prime

/-- The 25 primes conjectured not to be terms. -/
def exceptions : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 31, 37, 47, 61, 67, 71, 73, 89, 109, 137, 179, 211, 277, 337, 379,
    499, 557}

/-- The primes that are not terms of A094383 are exactly the 25 listed ones. -/
theorem main : {p : ℕ | p.Prime ∧ ¬ IsTerm p} = ↑exceptions := by
  sorry

end OMA.S_oeis_a094383
