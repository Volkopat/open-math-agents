import Mathlib

/-!
# A283929: Number of ways of writing n as a sum of a twin prime (A001097) and a squarefree semiprime (A006881).

Source: https://oeis.org/A283929
Credit: @azmiozgen

Conjecture (from the entry): a(n) > 0 for all n > 30.

Formalization notes:
* A twin prime (A001097) is a prime p with p - 2 or p + 2 prime; a squarefree semiprime
  (A006881) is p*q with primes p < q. a(n) > 0 is stated as the existence of a representation.
* Controls (computed): every n with 30 < n < 5000 has a representation.
-/

namespace OMA.S_oeis_a283929



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, 30 < n → ∃ t p q : ℕ, t.Prime ∧ ((t - 2).Prime ∨ (t + 2).Prime) ∧
      p.Prime ∧ q.Prime ∧ p < q ∧ t + p * q = n := by
  sorry

end OMA.S_oeis_a283929
