import Mathlib

/-!
# A232540: Numbers n such that (n(n+1)/2) modulo sigma(n) = 1.

Source: https://oeis.org/A232540
Credit: @agchua

Comment of A232540 (unsigned; the entry is by Jaroslav Krizek, Nov 25 2013):
  Conjecture: supersequence of A112774 (semiprimes of the form 6n+4).
A112774 (Semiprimes of the form 6n+4, offset 1) has the data 4, 10, 22, 34, 46, 58, 82, ...; a
semiprime is a product of two primes, not necessarily distinct. A232540 has offset 1, so its
terms are positive integers; sigma(n) is ArithmeticFunction.sigma 1 n, the sum of the divisors of
n, and n(n+1)/2 is an integer, so the natural-number division below is exact.

Range. The claim as printed fails only at the first term 4 = 2*2 of A112774: 4*5/2 = 10 and
10 mod sigma(4) = 10 mod 7 = 3, so 4 is not a term of A232540 (whose data starts 10, 22, 34, ...).
The statement below is the conjecture for all other terms of A112774: every semiprime n of the
form 6m+4 with n different from 4 is a term of A232540.
-/

namespace OMA.S_oeis_a232540

/-- n is a term of A232540: n >= 1 and (n(n+1)/2) mod sigma(n) = 1. -/
def IsA232540 (n : ℕ) : Prop :=
  1 ≤ n ∧ (n * (n + 1) / 2) % ArithmeticFunction.sigma 1 n = 1

/-- n is a term of A112774: n is a semiprime (a product of two primes) and n = 6m+4 for some
m >= 0, that is, n mod 6 = 4. -/
def IsA112774 (n : ℕ) : Prop :=
  (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q) ∧ n % 6 = 4

/-- The conjecture for every term of A112774 other than its first term 4: such a term is a term
of A232540. -/
theorem main : ∀ n : ℕ, IsA112774 n → n ≠ 4 → IsA232540 n := by
  sorry

end OMA.S_oeis_a232540
