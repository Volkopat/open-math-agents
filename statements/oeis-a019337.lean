import Mathlib

/-!
# A019337: Primes with primitive root 7

Source: https://oeis.org/A019337
Credit: @xor2k

The entry's text is a remark, not labelled as a conjecture: All terms apart from the first are
== 5, 11, 13, 15, 17, 23 (mod 28) since 7 is a quadratic residue modulo any other prime. By
Artin's conjecture, this sequence contains about 37.395% of all primes, that is, about 74.79% of
all primes == 5, 11, 13, 15, 17, 23 (mod 28).

Formalized claim: the first sentence, i.e. every term other than the first term 2 is congruent
to one of 5, 11, 13, 15, 17, 23 modulo 28. The second sentence is a density statement
conditional on Artin's conjecture and is not formalized.

Conventions: following the entry (and N. J. A. Sloane's comment there), a prime `p` is a term
when the multiplicative order of 7 modulo `p` is `p - 1`, i.e. `orderOf (7 : ZMod p) = p - 1`.
The first term is 2, for which `7 = 1` in `ZMod 2` has order `1 = 2 - 1`.
-/

namespace OMA.S_oeis_a019337

/-- Membership in A019337: `p` is a prime and 7 has multiplicative order `p - 1` modulo `p`. -/
def InA019337 (p : ℕ) : Prop :=
  p.Prime ∧ orderOf (7 : ZMod p) = p - 1

/-- Every term other than 2 is congruent to 5, 11, 13, 15, 17 or 23 modulo 28. -/
theorem main :
    ∀ p : ℕ, InA019337 p → p ≠ 2 → p % 28 ∈ ({5, 11, 13, 15, 17, 23} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a019337
