import Mathlib

/-!
# A077371: Fibonacci numbers whose internal digits form a Fibonacci number. Equivalently, Fibonacci numbers from which deleting the MSD and LSD leaves a Fibonacci number.

Source: https://oeis.org/A077371
Credit: @luciusacarr

The entry records one conjecture: the sequence is finite. (The source adds: no more terms
< 10^10000, Manfred Scheucher.) Its terms are 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 233, 610, 987.

Reading of the source:
* For a number `n` with `L` decimal digits, deleting the most and least significant digits
  leaves the number `(n % 10^(L-1)) / 10`. When `L ≤ 2` nothing is left, and the listed terms show
  that this counts as a Fibonacci number (13, 21, 34, 55, 89 and the one-digit Fibonacci numbers are
  terms): the formula gives `0 = F(0)` in that case. A leftover string with leading zeros is read
  as the number it denotes.
* With this reading the terms among the Fibonacci numbers `F(0), ..., F(5999)` are exactly the
  listed ones.
* The sequence lists Fibonacci values (1 appears twice, as F(1) = F(2)); finiteness of the
  sequence is finiteness of the set of such values.
-/

namespace OMA.S_oeis_a077371

/-- The number formed by the internal digits of `n` (delete the most and least significant
decimal digits); `0` if `n` has at most two digits. -/
def internal (n : ℕ) : ℕ := (n % 10 ^ ((Nat.digits 10 n).length - 1)) / 10

theorem main :
    {n : ℕ | (∃ i : ℕ, Nat.fib i = n) ∧ ∃ j : ℕ, Nat.fib j = internal n}.Finite := by
  sorry

end OMA.S_oeis_a077371
