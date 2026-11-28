import Mathlib

/-!
# OEIS A023408: the forced {5,6} and {3,4} end digits of powers of 2 add up to 9

Source: https://oeis.org/A023408 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (David W. Wilson), offset 1: If any power of 2 ends with k 5's and 6's, they must be the
first k terms of this sequence in reverse order. Data begins 6, 5, 6, 6, 6, 5. Formula:
Conjecture: a(n) + A023402(n) = 9, for n > 1. - J. Lowell, Nov 16 2020.
A023402 (David W. Wilson): If any power of 2 ends with k 3's and 4's, they must be the first k
terms of this sequence in reverse order. Data begins 4, 4, 3, 3, 3, 4.

Formalization notes:
* If a power 2^m ends with k digits that are all 5 or 6, then m >= k (a smaller power is below
  5 * 10^(k-1)), so these k digits form a number below 10^k divisible by 2^k. There is exactly
  one such number; `x56 k` builds it from the right, choosing at position k the digit 5 or 6
  that keeps divisibility by 2^(k+1). The proof file proves that `x56 k` is the only number
  below 10^k whose k digits are 5 or 6 and which is divisible by 2^k (and the same for `x34`).
* The first k terms in reverse order are the last k digits read from the left, so a(n) is the
  n-th digit from the right of `x56 n` (of `x56 k` for any k >= n, these agree). A023402(n) is
  defined in the same way from `x34`, with the digits 3 and 4.
* Controls proved in the proof file: a(1..6) = 6, 5, 6, 6, 6, 5 and A023402(1..6) =
  4, 4, 3, 3, 3, 4, as in the entries.
-/

namespace OMA.S_oeis_a023408

/-- The k-digit number with digits in {5, 6} divisible by 2^k, built digit by digit from the
right: the digit at position k is 5 or 6, whichever keeps divisibility by 2^(k+1). -/
def x56 : ℕ → ℕ
  | 0 => 0
  | k + 1 => if 2 ^ (k + 1) ∣ x56 k + 5 * 10 ^ k then x56 k + 5 * 10 ^ k else x56 k + 6 * 10 ^ k

/-- The k-digit number with digits in {3, 4} divisible by 2^k, built the same way. -/
def x34 : ℕ → ℕ
  | 0 => 0
  | k + 1 => if 2 ^ (k + 1) ∣ x34 k + 3 * 10 ^ k then x34 k + 3 * 10 ^ k else x34 k + 4 * 10 ^ k

/-- A023408(n): the n-th digit from the right of the {5,6} number of length n. -/
def a (n : ℕ) : ℕ := x56 n / 10 ^ (n - 1) % 10

/-- A023402(n): the n-th digit from the right of the {3,4} number of length n. -/
def b (n : ℕ) : ℕ := x34 n / 10 ^ (n - 1) % 10

/-- Lowell's conjecture: a(n) + A023402(n) = 9 for n > 1. -/
theorem main : ∀ n : ℕ, 1 < n → a n + b n = 9 := by
  sorry

end OMA.S_oeis_a023408
