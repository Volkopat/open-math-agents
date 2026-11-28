import Mathlib

/-!
# A241658: Smallest semiprime, sp, such that n - sp is a semiprime, or a(n)=0 if there is no such sp.

Source: https://oeis.org/A241658
Credit: @luciusacarr

The entry's comment: Conjecture: every number greater than 33 is a sum of two semiprimes. Only
1, 2, 3, 4, 5, 6, 7, 9, 11, 17, 22 & 33 cannot be so represented.

`main` states both sentences, as a conjunction, in the order the source gives them.

Reading of the source:
* A semiprime (A001358) is a product of two primes, not necessarily distinct: a natural number
  with exactly two prime factors counted with multiplicity (`ArithmeticFunction.cardFactors`).
* "Sum of two semiprimes" allows equal summands (8 = 4 + 4, a(8) = 4).
* The second sentence is about the positive integers (the sequence has offset 1), so 0 is
  excluded from the list of exceptions.
-/

namespace OMA.S_oeis_a241658

/-- A001358: `m` is a semiprime, a product of exactly two primes counted with multiplicity. -/
def IsSemiprime (m : ℕ) : Prop := ArithmeticFunction.cardFactors m = 2

/-- `n` is the sum of two semiprimes. -/
def IsSumTwoSemiprimes (n : ℕ) : Prop := ∃ a b : ℕ, IsSemiprime a ∧ IsSemiprime b ∧ n = a + b

theorem main :
    -- Every number greater than 33 is a sum of two semiprimes.
    (∀ n : ℕ, 33 < n → IsSumTwoSemiprimes n) ∧
    -- The only positive integers that are not are 1, 2, 3, 4, 5, 6, 7, 9, 11, 17, 22 and 33.
    (∀ n : ℕ, 0 < n →
      (¬ IsSumTwoSemiprimes n ↔ n ∈ ({1, 2, 3, 4, 5, 6, 7, 9, 11, 17, 22, 33} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a241658
