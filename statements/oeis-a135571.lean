import Mathlib

/-!
# A135571: Positive integers that are the difference of two positive triangular numbers in an odd number of ways.

Source: https://oeis.org/A135571
Credit: @agchua

In the comments of A135571:
  Conjecture. This sequence is just the sequence of positive integers that are either square,
  twice a square, or triangular, but not both square and triangular (A001110). (This has been
  verified for n up to 100000.)

T(k) = k(k+1)/2 is the k-th triangular number (an exact quotient); the positive triangular numbers
are T(k) with k >= 1. A way to write n as a difference of two positive triangular numbers is a pair
of indices 1 <= j < i with T(i) - T(j) = n, i.e. T(i) = T(j) + n. Every such pair has i <= n,
because T(i) - T(j) >= T(i) - T(i-1) = i; so counting the pairs in Icc 1 n x Icc 1 n loses nothing.
The entry's examples agree: 6 = 21 - 15 (1 way), 9 = 10 - 1 = 15 - 6 = 45 - 36 (3 ways),
5 = 6 - 1 = 15 - 10 (2 ways).
The conjecture says: a positive integer n is a term (an odd number of ways) if and only if n is a
square, twice a square or triangular, and n is not both a square and triangular.
-/

namespace OMA.S_oeis_a135571

/-- The k-th triangular number k(k+1)/2. -/
def T (k : ℕ) : ℕ := k * (k + 1) / 2

/-- The number of ways to write n as T(i) - T(j) with 1 <= j < i. -/
def ways (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p => p.2 < p.1 ∧ T p.1 = T p.2 + n)).card

/-- Conjecture: for n >= 1, n is the difference of two positive triangular numbers in an odd number
of ways if and only if n is a square, twice a square or triangular, but not both a square and
triangular. -/
theorem main : ∀ n : ℕ, 0 < n →
    (Odd (ways n) ↔
      ((IsSquare n ∨ (∃ m : ℕ, n = 2 * m ^ 2) ∨ ∃ k : ℕ, n = T k) ∧
        ¬ (IsSquare n ∧ ∃ k : ℕ, n = T k))) := by
  sorry

end OMA.S_oeis_a135571
