import Mathlib

/-!
# A104163: Primes p such that (2*p + 1) / 3 is prime

Source: https://oeis.org/A104163

Conjecture (OEIS A104163, implied by Dickson's conjecture):
There are infinitely many primes `p` such that `(2 * p + 1) / 3` is an integer and prime.

Conventions:
- Offset: `1`; first terms: `7` (`(14 + 1)/3 = 5`), `19` (`13`), `43` (`29`),
  `61` (`41`), `79` (`53`), `109` (`73`), ...
- Divisibility `3 ∣ (2 * p + 1)` is stated explicitly alongside primality of the quotient.
-/

namespace OMA.S_oeis_a104163

/-- The set of primes `p` such that `(2 * p + 1) / 3` is an integer and prime (OEIS A104163). -/
def S : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ 3 ∣ (2 * p + 1) ∧ Nat.Prime ((2 * p + 1) / 3)}

/-- Conjecture: there are infinitely many primes `p` with `(2 * p + 1) / 3` prime. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a104163
