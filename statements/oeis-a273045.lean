import Mathlib

/-!
# A273045: Fibonacci numbers with digits in nondecreasing order.

Source: https://oeis.org/A273045
Credit: @keiichisince1986-bot

A273045 lists the Fibonacci numbers whose decimal digits are in nondecreasing order:
`0, 1, 1, 2, 3, 5, 8, 13, 34, 55, 89, 144, 233, 377`.
The entry states: Conjecture: The sequence is finite, with 377 being the last term
(verified up to Fibonacci(10^8)).

Conventions:
- The Fibonacci numbers are `Nat.fib n` for `n : ℕ` (`Nat.fib 0 = 0`, `Nat.fib 1 = 1`), as in
  A000045. The OEIS data list `1` twice (as `F(1)` and `F(2)`); we state the conjecture about the
  set of terms, so repetitions do not matter.
- `Nat.digits 10 m` lists the decimal digits of `m` from the least significant one, so
  `(Nat.digits 10 m).reverse` lists them as written, from the leading digit. The digits are in
  nondecreasing order when this list is pairwise `≤` (equivalently, sorted). For `m = 0` the
  digit list is empty, which matches the OEIS convention that `0` (a single digit) qualifies.
- The sequence is finite with last term `377` exactly when `377` is the greatest element of the
  set of terms: `IsGreatest S 377` says that `377 ∈ S` and every element of `S` is at most `377`,
  so `S` is finite.
-/

namespace OMA.S_oeis_a273045

theorem main :
    IsGreatest {m : ℕ | (∃ n : ℕ, m = Nat.fib n) ∧ (Nat.digits 10 m).reverse.Pairwise (· ≤ ·)}
      377 := by
  sorry

end OMA.S_oeis_a273045
