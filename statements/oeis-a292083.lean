import Mathlib

/-!
# A292083: Odd numbers k that can be uniquely expressed as (2*p + 1)/q for some prime p and some prime q < 2*k.

Source: https://oeis.org/A292083
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A292083 (Arkadiusz Wesolowski, Sep 08 2017): the
sequence is finite and complete.

Conventions:
* The sequence has offset 1 (data 3, 7, 11, 19, 23, 37, 47, 227, 313, ...).
* k = (2*p + 1)/q is written as k*q = 2*p + 1. `Uniquely expressed` is the existence of exactly
  one pair (p, q) of primes with q < 2*k and k*q = 2*p + 1 (`∃!` over pairs).
* `Finite and complete` is stated as: the set of all terms equals the set of the nine terms listed
  in the entry.
-/

namespace OMA.S_oeis_a292083

/-- The conjecture recorded in A292083. -/
theorem main : {k : ℕ | Odd k ∧ ∃! t : ℕ × ℕ, t.1.Prime ∧ t.2.Prime ∧ t.2 < 2 * k ∧
    k * t.2 = 2 * t.1 + 1} = ({3, 7, 11, 19, 23, 37, 47, 227, 313} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a292083
