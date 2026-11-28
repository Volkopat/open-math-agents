import Mathlib

/-!
# A144642: Positive numbers that are not the sum of a triangular number, a square and a Fibonacci number.

Source: https://oeis.org/A144642
Credit: @agchua

Comment of A144642 (the entry is by Kurt Foster, Jan 25 2009), verbatim:
  Prompted by a conjecture of _Zhi-Wei Sun_ (now known not to be true) that every number can be
  written in the stated form.
The entry's next comment writes the stated form as n = x^2 + y*(y+1)/2 + F_m with m >= 0, and the
entry lists the counterexamples, the first being a(1) = 3970902.

Formalisation. The text asserts that Sun's conjecture is false, so the statement is the negation
of the conjecture: it is not true that every positive integer n can be written as
n = x^2 + y*(y+1)/2 + F_m with natural numbers x, y, m (F_m = Nat.fib m, F_0 = 0, so zero
summands are allowed, which only makes the conjecture weaker and its negation stronger).
-/

namespace OMA.S_oeis_a144642

/-- Sun's conjecture (every number is a triangular number plus a square plus a Fibonacci number)
is not true. -/
theorem main : ¬ ∀ n : ℕ, 0 < n → ∃ x y m : ℕ, n = x ^ 2 + y * (y + 1) / 2 + Nat.fib m := by
  sorry

end OMA.S_oeis_a144642
