import Mathlib

/-!
# A095116: a(n) = prime(n) + n - 1.

Source: https://oeis.org/A095116
Credit: @agchua

Comment of A095116 by N. J. A. Sloane, Mar 28 2024, verbatim:
  On March 23 2024, Davide Rotondo sent me an email with the following conjecture.
  (I've simplified it a bit.)
  For a positive integer n, define a sequence b by b(0) = n; b(i) = n - pi(b(i-1)) for i >= 1,
  where pi(x) = number of primes <= x.
  The conjecture is that after some initial terms, b becomes periodic with period length 1 or 2,
  and the n for which the period is 2 are 3 together with the present sequence, that is,
  2, 3, 4, 7, 10, 15, 18, 23, 26, 31, 38, 41, 48, ...
The entry also contains a proof by Robert Israel (Mar 26 2024) of the periodicity part.

Formalised: pi is Nat.primeCounting, b n i is the sequence b for the start value n, and
A095116(m) = prime(m) + m - 1 for m >= 1 with prime(m) = Nat.nth Nat.Prime (m - 1)
(offset 1: 2, 4, 7, 10, ...). For every n >= 1: (1) there is N with b(i+2) = b(i) for all
i >= N (eventually periodic with period length 1 or 2); (2) the period is 2, that is, b is
not eventually constant, exactly when n = 3 or n is a term of A095116.
-/

namespace OMA.S_oeis_a095116

/-- b n 0 = n and b n (i + 1) = n - pi(b n i), with pi = Nat.primeCounting. -/
noncomputable def b (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => n - Nat.primeCounting (b n i)

/-- A095116(m) = prime(m) + m - 1, where prime(m) = Nat.nth Nat.Prime (m - 1) for m >= 1. -/
noncomputable def a (m : ℕ) : ℕ := Nat.nth Nat.Prime (m - 1) + m - 1

/-- Rotondo's conjecture: b is eventually periodic with period length 1 or 2, and it is not
eventually constant exactly for n = 3 and for the terms of A095116. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (∃ N : ℕ, ∀ i : ℕ, N ≤ i → b n (i + 2) = b n i) ∧
    ((¬ ∃ N : ℕ, ∀ i : ℕ, N ≤ i → b n (i + 1) = b n i) ↔
      (n = 3 ∨ ∃ m : ℕ, 1 ≤ m ∧ n = a m)) := by
  sorry

end OMA.S_oeis_a095116
