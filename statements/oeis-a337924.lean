import Mathlib

/-!
# A337924: Odd numbers, x, such that for all primes (p,q) such that x = p + 2q, x + 2p and x + 2q are composite.

Source: https://oeis.org/A337924
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A337924 (Jud McCranie, Oct 09 2020): The sequence is
conjectured to be finite and full.

Conventions:
* The sequence has offset 1 (data 1, 3, 5, 59, 151, ...).
* The terms are the odd natural numbers x such that for all primes p, q with x = p + 2*q, both x +
  2*p and x + 2*q are composite (these numbers exceed 1, so `composite` is `not prime`). Odd
  numbers with no such representation (1, 3, 5) satisfy the condition vacuously, as in the data.
* `Finite and full` is stated as: the set of all terms equals the set of the five terms 1, 3, 5,
  59, 151 listed in the entry.
-/

namespace OMA.S_oeis_a337924

/-- The conjecture recorded in A337924. -/
theorem main : {x : ℕ | Odd x ∧ ∀ p q : ℕ, p.Prime → q.Prime → x = p + 2 * q →
    ¬ (x + 2 * p).Prime ∧ ¬ (x + 2 * q).Prime} = ({1, 3, 5, 59, 151} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a337924
