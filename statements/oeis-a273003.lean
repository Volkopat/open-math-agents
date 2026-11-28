import Mathlib

/-!
# A273003: Arrange the base 10 digits of the n-th Fibonacci number in descending order.

Source: https://oeis.org/A273003
Credit: @eltociear

The source states, in its COMMENTS section:
  Conjecture: the largest Fibonacci number F(n) with its base 10 digits already sorted in
  descending order is F(16) = 987.

Reading of the conjecture. F(n) is A000045 with F(0) = 0 and F(1) = 1, which is Mathlib's
Nat.fib. The base 10 digits of a natural number are the list Nat.digits 10 n, which lists them
from the least significant one; a number has its base 10 digits sorted in descending order exactly
when that list, read from the last entry to the first, is non-increasing, i.e. every digit is at
least every digit written after it. The conjecture then says that 987 is the greatest element of
the set of Fibonacci numbers whose base 10 digits are sorted in descending order: 987 itself is
one of them because Nat.fib 16 = 987 and 9 >= 8 >= 7, and the conjecture is that no larger
Fibonacci number has that property.
-/

namespace OMA.S_oeis_a273003

/-- The base 10 digits of n, read in the usual order from the most significant one, are in
descending order (each digit is at least every digit after it). Nat.digits 10 n lists the
digits from the least significant one, hence the reverse. -/
def IsDescendingDigits (n : ℕ) : Prop :=
  List.Pairwise (fun a b : ℕ => b ≤ a) (Nat.digits 10 n).reverse

theorem main : IsGreatest {x : ℕ | ∃ n : ℕ, Nat.fib n = x ∧ IsDescendingDigits x} 987 := by
  sorry

end OMA.S_oeis_a273003
-- ci: re-run check-proof
