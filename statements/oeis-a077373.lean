import Mathlib

/-!
# A077373: Fibonacci numbers whose external digits as well as internal digits form a Fibonacci number.

Source: https://oeis.org/A077373
Credit: @luciusacarr

The entry records one conjecture: the sequence is finite. It also asks "Is there any term > 89 in
this sequence?", which is a question and is not stated. Its terms are 0, 1, 1, 2, 3, 5, 8, 13, 21,
34, 55, 89.

Reading of the source (as in A077371, of which this is a subsequence):
* For a number `n` with `L ≥ 2` decimal digits, the external digits are its most and least
  significant digits, forming the two-digit number `10 * (n / 10^(L-1)) + n % 10`; for a one-digit
  `n` the external digits form `n` itself (the one-digit Fibonacci numbers are terms).
* The internal digits are what remains after deleting the most and least significant digits:
  the number `(n % 10^(L-1)) / 10`. When `L ≤ 2` nothing is left, and the listed terms (13, 21,
  34, 55, 89) show that this counts as a Fibonacci number: the formula gives `0 = F(0)`.
* With this reading the terms among the Fibonacci numbers `F(0), ..., F(3999)` are exactly the
  listed ones. Finiteness of the sequence is finiteness of the set of such values.
-/

namespace OMA.S_oeis_a077373

/-- The number formed by the internal digits of `n` (delete the most and least significant
decimal digits); `0` if `n` has at most two digits. -/
def internal (n : ℕ) : ℕ := (n % 10 ^ ((Nat.digits 10 n).length - 1)) / 10

/-- The number formed by the external digits of `n` (its most and least significant decimal
digits); `n` itself if `n` has one digit. -/
def external (n : ℕ) : ℕ :=
  if n < 10 then n else 10 * (n / 10 ^ ((Nat.digits 10 n).length - 1)) + n % 10

theorem main :
    {n : ℕ | (∃ i : ℕ, Nat.fib i = n) ∧ (∃ j : ℕ, Nat.fib j = external n) ∧
      ∃ j : ℕ, Nat.fib j = internal n}.Finite := by
  sorry

end OMA.S_oeis_a077373
