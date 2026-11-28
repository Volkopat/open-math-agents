import Mathlib

/-!
# A084352: Minimum digit out of both prime factors of palindromic brilliant numbers.

Source: https://oeis.org/A084352
Credit: @avivorly

A brilliant number (OEIS A078972) is a semiprime `p * q` (`p`, `q` prime, not necessarily distinct)
whose two prime factors have the same number of decimal digits. A084352 lists, for the palindromic
brilliant numbers in increasing order (4, 6, 9, 121, 323, ...), the smallest decimal digit occurring
in the two prime factors (for example 989 = 23 * 43 gives 2).

Conjecture in the entry (Jason Earls, 2003): a(n) is never greater than 3.

A brilliant number has exactly one factorization `p * q` with `p ≤ q`, and the smallest digit of the
two factors does not depend on their order, so the conjecture says: for all primes `p`, `q` with the
same number of decimal digits such that `p * q` is a decimal palindrome, the smallest decimal digit
occurring in `p` or in `q` is at most 3.
-/

namespace OMA.S_oeis_a084352

/-- The smallest decimal digit occurring in `p` or in `q`. -/
noncomputable def minDigit (p q : ℕ) : ℕ :=
  sInf {d : ℕ | d ∈ Nat.digits 10 p ∨ d ∈ Nat.digits 10 q}

theorem main : ∀ p q : ℕ, p.Prime → q.Prime →
    (Nat.digits 10 p).length = (Nat.digits 10 q).length →
    (Nat.digits 10 (p * q)).reverse = Nat.digits 10 (p * q) →
    minDigit p q ≤ 3 := by
  sorry

end OMA.S_oeis_a084352
