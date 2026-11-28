import Mathlib

/-!
# A373049: Integers k such that the product of the nonzero digits of the k-th Fibonacci number (A000045) is a perfect power.

Source: https://oeis.org/A373049
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A373049 (Gonzalo Martínez, May 20 2024): this sequence
has infinitely many terms.

Conventions:
* The sequence has offset 1 (data 0, 1, 2, 6, 10, 12, 19, 21, 22, 27, 31, 46, ...).
* The k-th Fibonacci number is `Nat.fib k`; the product of its nonzero decimal digits is the
  product of the list of nonzero entries of `Nat.digits 10 (Nat.fib k)` (the empty product, for k
  = 0, is 1).
* A perfect power is a number of the form a^b with b >= 2; this includes 1 = 1^2, in agreement
  with the terms 0, 1, 2 of the sequence.
* `The sequence is infinite` / `has infinitely many terms` is rendered as `Set.Infinite` of the
  set of all numbers with the defining property of the OEIS name.
-/

namespace OMA.S_oeis_a373049

/-- The conjecture recorded in A373049. -/
theorem main : Set.Infinite {k : ℕ | ∃ a b : ℕ, 2 ≤ b ∧
    a ^ b = ((Nat.digits 10 (Nat.fib k)).filter (fun d => d ≠ 0)).prod} := by
  sorry

end OMA.S_oeis_a373049
