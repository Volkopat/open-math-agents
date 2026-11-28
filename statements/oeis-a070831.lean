import Mathlib

/-!
# A070831: Palindromic primes with digit sum = 11.

Source: https://oeis.org/A070831
Credit: @matchalabubu15

Conjecture (stated in A070831): "The sequence is unbounded."

Formalization notes:
* Base 10 throughout: the entry carries the OEIS keyword `base`, and its first terms
  (191, 353, 13331, ...) are palindromes with digit sum 11 in decimal.
* The digits of a number are given by `Nat.digits 10`, which lists them from least to most
  significant, with no leading zeros.
* A number is palindromic when that list of digits equals its reverse.
* The digit sum is the sum of that list.
* The sequence lists the numbers with these properties in increasing order, so it is represented
  by the set of its terms. "The sequence is unbounded" is stated as: this set of natural numbers
  has no upper bound (`¬ BddAbove`). A finite sequence would be bounded, so the statement also
  asserts that there are infinitely many such primes.
-/

namespace OMA.S_oeis_a070831

/-- The terms of A070831: primes that are palindromes in base 10 and have decimal digit sum 11. -/
def A070831 : Set ℕ :=
  {p : ℕ | p.Prime ∧ (Nat.digits 10 p).reverse = Nat.digits 10 p ∧ (Nat.digits 10 p).sum = 11}

/-- The conjecture of A070831: the sequence is unbounded. -/
theorem main : ¬ BddAbove A070831 := by
  sorry

end OMA.S_oeis_a070831
