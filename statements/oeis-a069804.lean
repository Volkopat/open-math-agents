import Mathlib

/-!
# A069804: Larger of the two consecutive palindromic primes.

Source: https://oeis.org/A069804
Credit: @keiichisince1986-bot

A069804 lists the larger member of each pair of consecutive primes that are both palindromes:
`3, 5, 7, 11, 191, 797, 929` (the pairs are `(2, 3), (3, 5), (5, 7), (7, 11), (181, 191),`
`(787, 797), (919, 929)`; the smaller members form A069803).
The entry states: Conjectured to be complete.

Conventions:
- Two consecutive palindromic primes means two consecutive primes `p < q` (no prime strictly
  between them) that are both palindromes. This is the reading the data follow: `11` and `101`
  are consecutive among palindromic primes but are not consecutive primes, and `101` is not a term.
- `IsPalindrome n`: the decimal digit list of `n` equals its reverse.
- `IsNextPrime p q`: `q` is the least prime greater than `p`.
- Complete means that the data list every term, so the conjecture says that the set of such
  larger members is exactly `{3, 5, 7, 11, 191, 797, 929}`.
-/

namespace OMA.S_oeis_a069804

/-- `n` is a palindrome in base 10. -/
def IsPalindrome (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- `q` is the least prime greater than `p`. -/
def IsNextPrime (p q : ℕ) : Prop :=
  q.Prime ∧ p < q ∧ ∀ r : ℕ, p < r → r < q → ¬ r.Prime

theorem main :
    {q : ℕ | IsPalindrome q ∧ ∃ p : ℕ, p.Prime ∧ IsPalindrome p ∧ IsNextPrime p q} =
      {3, 5, 7, 11, 191, 797, 929} := by
  sorry

end OMA.S_oeis_a069804
