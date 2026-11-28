import Mathlib

/-!
# A172487: Lesser of twin primes in A172240.

Source: https://oeis.org/A172487
Credit: @rickmanelius

Comment in the entry (unsigned; the entry is by Giovanni Teofilatto, Nov 21 2010): For a(n) > 3,
the first differences of the sequence are divisible by 6. (Is this a conjecture or a theorem?)

Formalization notes:
* A181669 is the set of primes p of the form 6n-1 such that p-1 is a semiprime and p+2 is prime
  or prime squared. Of the form 6n-1 is p % 6 = 5 (the Maple code of A181669 tests
  modp(n,6) = 5). p - 1 is a semiprime when it has exactly two prime factors counted with
  multiplicity: Mathlib's `ArithmeticFunction.cardFactors` (bigomega, as in the Maple code)
  equals 2. Prime squared means q ^ 2 for a prime q (A000430 lists the primes and the squares of
  primes).
* A172240 is the set of odd primes not in A181669.
* A172487 is A001359 INTERSECT A172240 (formula of the entry): p is a term when p is in A172240
  and p and p + 2 are both prime, that is, p is the lesser of a pair of twin primes (A001359).
* `a n` is the n-th term in increasing order, offset 1. `Nat.nth` counts from 0, so
  a(n) = Nat.nth InA172487 (n - 1). These definitions reproduce the 50 listed terms 3, 17, 29,
  41, 71, 101, 137, 149, ..., 1949, 1997, and the listed data of A181669 (5, 11, 23, 47, 59, ...)
  and of A172240 (3, 7, 13, 17, 19, 29, ...), checked by computer.
* The first differences are a(n+1) - a(n), and the condition a(n) > 3 is on the earlier term.
  Only a(1) = 3 is excluded, and indeed a(2) - a(1) = 17 - 3 = 14 is not divisible by 6. The
  difference is taken in the integers.
* It is not known that the sequence is infinite (every term is the lesser of a pair of twin
  primes). If it were finite, its last term would have no next term, and `Nat.nth` would return
  the junk value 0, which is not a term. The hypothesis InA172487 (a (n + 1)) says exactly that
  a(n+1) exists, so the statement claims nothing about junk values. The hypothesis 3 < a n
  rules out a junk a(n) (junk values are 0).
-/

namespace OMA.S_oeis_a172487

/-- A000430: n is a prime or the square of a prime. -/
def IsPrimeOrPrimeSq (n : ℕ) : Prop := n.Prime ∨ ∃ q : ℕ, q.Prime ∧ n = q ^ 2

/-- A181669: p is a prime of the form 6n-1, p - 1 is a semiprime, and p + 2 is prime or prime
squared. -/
def InA181669 (p : ℕ) : Prop :=
  p.Prime ∧ p % 6 = 5 ∧ ArithmeticFunction.cardFactors (p - 1) = 2 ∧ IsPrimeOrPrimeSq (p + 2)

/-- A172240: p is an odd prime not in A181669. -/
def InA172240 (p : ℕ) : Prop := p.Prime ∧ Odd p ∧ ¬ InA181669 p

/-- A172487 = A001359 INTERSECT A172240: p is in A172240 and p, p + 2 are both prime. -/
def InA172487 (p : ℕ) : Prop := InA172240 p ∧ p.Prime ∧ (p + 2).Prime

/-- A172487(n) for n ≥ 1: the n-th term in increasing order (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth InA172487 (n - 1)

/-- For a(n) > 3 the first difference a(n+1) - a(n) is divisible by 6 (for every n ≥ 1 such that
a(n+1) is a term of the sequence). -/
theorem main : ∀ n : ℕ, 1 ≤ n → 3 < a n → InA172487 (a (n + 1)) →
    (6 : ℤ) ∣ (a (n + 1) : ℤ) - (a n : ℤ) := by
  sorry

end OMA.S_oeis_a172487
