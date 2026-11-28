import Mathlib

/-!
# A307368: Minimal positive a(n) such that 2*a(n)*prime(n)-1 equals another prime

Source: https://oeis.org/A307368
Credit: @niclorusso

Conjecture (in the comments of A307368): A more general form of Rassias's conjecture states that
for every positive integer a there are two primes p and q such that 2*a*p = q+1.

Conventions:
* a ranges over the positive integers and p, q over the primes.
-/

namespace OMA.S_oeis_a307368

/-- The general form of Rassias's conjecture recorded in A307368: for every positive integer `a`
there are primes `p` and `q` with `2 * a * p = q + 1`. -/
theorem main : ∀ a : ℕ, 0 < a → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2 * a * p = q + 1 := by
  sorry

end OMA.S_oeis_a307368
