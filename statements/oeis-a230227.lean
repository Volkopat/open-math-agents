import Mathlib

/-!
# A230227: Primes p with 3*p - 10 also prime.

Source: https://oeis.org/A230227
Credit: @prasledi

Conjecture (Zhi-Wei Sun, in the COMMENTS of A230227): for any integer n > 4 not equal to 76,
we have 2*n = p + q for some terms p and q from the sequence.

Formalization notes:
* A term is a prime p such that 3p - 10 is prime. The subtraction is in ℕ: for p = 2, 3 the real
  value 3p - 10 is negative (so not prime), and the truncated value 0 is not prime either, so the
  set is the same. The definition reproduces the OEIS data 5, 7, 11, 13, 17, ..., 409 (#eval).
* p and q may be equal (as in Goldbach-type statements; the conjecture does not ask for distinct
  terms). The integers n are the natural numbers n > 4 with n ≠ 76.
-/

namespace OMA.S_oeis_a230227

/-- `p` is a term of A230227: `p` and `3p - 10` are prime. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ (3 * p - 10).Prime

/-- Sun's conjecture on A230227. -/
theorem main :
    ∀ n : ℕ, 4 < n → n ≠ 76 → ∃ p q : ℕ, IsTerm p ∧ IsTerm q ∧ 2 * n = p + q := by
  sorry

end OMA.S_oeis_a230227
