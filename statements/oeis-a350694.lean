import Mathlib

/-!
# A350694: numbers `p*q + r` with `p, q, r` prime and `p + q + r` prime

Source: https://oeis.org/A350694
Credit: @Lenqth

A350694 lists the positive integers that can be written as `p*q + r` where `p, q, r` are primes
(not necessarily distinct) such that `p + q + r` is also prime. For example `14 = 3*3 + 5` with
`3 + 3 + 5 = 11` prime.

Formalizes the conjecture in the comments of A350694: the sequence contains all even positive
integers except `2, 4, 6, 10, 12, 30, 48, 60`. We read "except" as saying these eight are exactly
the even positive integers missing from the sequence.
-/

namespace OMA.S_oeis_a350694

/-- `n` is a term of A350694: `n = p*q + r` with `p, q, r` and `p + q + r` all prime. -/
def IsTerm (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ (p + q + r).Prime ∧ n = p * q + r

/-- The even positive integers that are not terms are exactly `2, 4, 6, 10, 12, 30, 48, 60`. -/
theorem main :
    {n : ℕ | 0 < n ∧ Even n ∧ ¬ IsTerm n} = {2, 4, 6, 10, 12, 30, 48, 60} := by
  sorry

end OMA.S_oeis_a350694
