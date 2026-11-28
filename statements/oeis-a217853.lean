import Mathlib

/-!
# A217853: Fermat pseudoprimes to base 3 of the form (3^(4*k + 2) - 1)/8.

Source: https://oeis.org/A217853
Credit: @prasledi

Conjecture (in the COMMENTS of A217853): there are infinitely many Fermat pseudoprimes to base 3
of the form (3^(4*k + 2) - 1)/8, where k is a natural number.

Formalization notes:
* Fermat pseudoprime to base 3 is Mathlib's `Nat.FermatPsp n 3`: n > 1, n is not prime and
  n divides 3^(n-1) - 1.
* 8 divides 3^(4k+2) - 1 = 9^(2k+1) - 1 for every k, so the division is exact. k ranges over
  the natural numbers (k = 0 gives 1, not a pseudoprime; k = 1 gives 91 = 7 * 13, the first term).
* "Infinitely many pseudoprimes of this form" is stated as: the set of k for which
  (3^(4k+2) - 1)/8 is a base-3 Fermat pseudoprime is infinite. Different k give different
  numbers (the map k -> (3^(4k+2) - 1)/8 is strictly increasing), so this is equivalent to the set
  of such pseudoprimes being infinite.
* A later comment in the entry notes that it is true when 2k+1 is prime (Cipolla's construction).
-/

namespace OMA.S_oeis_a217853

/-- The conjecture of A217853. -/
theorem main : {k : ℕ | Nat.FermatPsp ((3 ^ (4 * k + 2) - 1) / 8) 3}.Infinite := by
  sorry

end OMA.S_oeis_a217853
