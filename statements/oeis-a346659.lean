import Mathlib

/-!
# A346659: Primes that are not of the form p*q +- 2 where p and q are primes (not necessarily distinct).

Source: https://oeis.org/A346659
Credit: @luciusacarr

Data: 3, 5, 29, 43, 61, 73, 101, 103, 107, 137, ...

Conjecture (from the entry): this sequence is infinite. `main` states it.

Reading of the source:
* A prime `r` is of the form `p*q ± 2` when `r = p*q + 2` or `r = p*q - 2` for primes `p, q`
  (not necessarily distinct). Example: 2 = 2*2 - 2 is not a term; 3 is a term since neither 1
  nor 5 is a product of two primes.
* With this reading the terms below 1100 are exactly the listed ones (checked numerically).
-/

namespace OMA.S_oeis_a346659

/-- The terms of A346659. -/
def S : Set ℕ :=
  {r | r.Prime ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (r = p * q + 2 ∨ r + 2 = p * q)}

theorem main :
    -- The sequence is infinite.
    S.Infinite := by
  sorry

end OMA.S_oeis_a346659
