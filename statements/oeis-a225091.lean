import Mathlib

/-!
# A225091: The odd part of the digit sum of 7^n.

Source: https://oeis.org/A225091
Credit: @prasledi

Conjecture (in the COMMENTS of A225091): the sequence contains all primes > 3.

Formalization notes:
* Offset 0: a(n) is the odd part of the sum of the decimal digits of 7^n, for n >= 0.
* The decimal digit sum of m is `(Nat.digits 10 m).sum`; the odd part of m >= 1 is
  m / 2^(v_2(m)), with v_2(m) = `m.factorization 2`. The digit sum of 7^n is >= 1.
* The definition reproduces the OEIS data 1, 7, 13, 5, 7, 11, 7, 25, 31, 7, 43, 49, 37, 13, 29, 1,
  13, 29, 73, 79 (checked with #eval for n = 0..19).
* "Contains all primes > 3": every prime p > 3 equals a(n) for some n.
-/

namespace OMA.S_oeis_a225091

/-- The odd part of `m`: `m` divided by the largest power of 2 dividing it. -/
def oddPart (m : ℕ) : ℕ := m / 2 ^ (m.factorization 2)

/-- `a n`: the odd part of the decimal digit sum of `7 ^ n`. -/
def a (n : ℕ) : ℕ := oddPart (Nat.digits 10 (7 ^ n)).sum

/-- The conjecture of A225091: every prime greater than 3 is a term. -/
theorem main : ∀ p : ℕ, p.Prime → 3 < p → ∃ n : ℕ, a n = p := by
  sorry

end OMA.S_oeis_a225091
