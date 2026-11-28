import Mathlib

/-!
# On nontotient Fibonacci numbers

The conjecture uses the Fibonacci numbers at indices divisible by six.
The totient preimage is required to be positive, as in the source's
definition of a nontotient. The index parameter may be zero.

Original question
https://mathoverflow.net/questions/368139

Related sequence
https://oeis.org/A335976

Formalization by @llostinthesauce.
-/

namespace OMA.S_mo_368139

/-- Infinitely many indices `t` have no positive totient preimage for `F_(6t)`. -/
theorem main :
    {t : ℕ | ¬ ∃ m : ℕ, 0 < m ∧ Nat.totient m = Nat.fib (6 * t)}.Infinite := by
  sorry

end OMA.S_mo_368139
