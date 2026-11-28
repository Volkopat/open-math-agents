import Mathlib

/-!
# A210184: Number of distinct residues of all factorials mod prime(n).

Source: https://oeis.org/A210184
Credit: @prasledi

Conjecture (in the COMMENTS of A210184): a(n)/p_n > 1/2.

Formalization notes:
* a(n) is the number of distinct values of m! mod p, m = 0, 1, 2, ..., for p = prime(n).
  The residue 0 is counted (it is taken by m! for every m >= p), as in the OEIS example:
  modulo 7 the residues are 0, 1, 2, 3, 6, so a(4) = 5. Including m = 0 changes nothing,
  since 0! = 1!.
* The set of residues is a subset of {0, ..., p-1}, hence finite, so `Set.ncard` is its
  number of elements.
* Since n ranges over all n >= 1, p ranges over all primes. a(n)/p_n > 1/2 is stated in the
  natural numbers as p < 2 * a(n).
* The OEIS data (first 20 terms) is reproduced by this definition, and the inequality holds
  for all primes p < 3000.
-/

namespace OMA.S_oeis_a210184

/-- A210184 as a function of the prime: the number of distinct residues of `m!` modulo `p`. -/
noncomputable def numFactorialResidues (p : ℕ) : ℕ :=
  (Set.range fun m : ℕ => Nat.factorial m % p).ncard

/-- The conjecture of A210184: for every prime `p`, more than half of the residues modulo `p`
are residues of factorials. -/
theorem main : ∀ p : ℕ, p.Prime → p < 2 * numFactorialResidues p := by
  sorry

end OMA.S_oeis_a210184
