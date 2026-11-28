import Mathlib

/-!
# A227576: Numbers k such that F(3*k)/(2*F(k)) is prime, where F(m) is the m-th Fibonacci number.

Source: https://oeis.org/A227576
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A227576 (Thomas Ordowski, Jul 16 2013): this sequence
is infinite.

Conventions:
* The sequence has offset 1 (data 5, 7, 11, 13, 17, 31, 37, 41, 67, 107, 151, 257, ...).
* F(m) is the Fibonacci number `Nat.fib m` (F(0) = 0, F(1) = 1). `F(3*k)/(2*F(k)) is prime`
  requires the quotient to be an integer, so it is stated as: 2*F(k) divides F(3*k) and the (then
  exact) natural-number quotient is prime. For k = 0 the divisor is 0 and the quotient 0 is not
  prime.
* `The sequence is infinite` / `has infinitely many terms` is rendered as `Set.Infinite` of the
  set of all numbers with the defining property of the OEIS name.
-/

namespace OMA.S_oeis_a227576

/-- The conjecture recorded in A227576. -/
theorem main : Set.Infinite {k : ℕ | 2 * Nat.fib k ∣ Nat.fib (3 * k) ∧
    (Nat.fib (3 * k) / (2 * Nat.fib k)).Prime} := by
  sorry

end OMA.S_oeis_a227576
