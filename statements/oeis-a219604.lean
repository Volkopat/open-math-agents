import Mathlib

/-!
# A219604: Smallest prime p such that 2n+1 = 4q + p for some odd prime q, or 0 if no such prime exists.

Source: https://oeis.org/A219604
Credit: @prasledi

Conjecture (in the COMMENTS of A219604): except m = 77, all odd numbers > 9 are of the form
m = p + 4*q where p and q are prime numbers.

Formalization notes:
* The conjecture is stated exactly as written in the comment: p and q are arbitrary primes.
  The sequence name says odd prime q, but the data uses q = 2 (a(5) = 3 because
  11 = 4*2 + 3, a(6) = 5 because 13 = 4*2 + 5), and the conjecture itself only says that p
  and q are prime numbers.
* m = 77 is the only exception in the data (a(38) = 0, with 2*38 + 1 = 77). A brute-force
  search confirms that every other odd m with 9 < m < 40000 has such a representation.
* Odd numbers > 9 are the odd m with 9 < m; m = 77 is excluded.
-/

namespace OMA.S_oeis_a219604

/-- The conjecture of A219604: every odd `m > 9` other than `77` is `p + 4q` with `p`, `q`
prime. -/
theorem main :
    ∀ m : ℕ, Odd m → 9 < m → m ≠ 77 → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p + 4 * q := by
  sorry

end OMA.S_oeis_a219604
