import Mathlib

/-!
# A002385: Palindromic primes

Source: https://oeis.org/A002385
Credit: @niclorusso

Conjecture (Ivan N. Ianakiev, in the comments of A002385): The only primes with palindromic prime
indices that are palindromic primes themselves are 3, 5 and 11. Tested for the primes with the
first 8000000 palindromic prime indices.

Conventions:
* A palindromic prime (a term of A002385) is a prime whose decimal expansion is a palindrome:
  `(Nat.digits 10 n).Palindrome`, Mathlib's `List.Palindrome` on the base-10 digits.
* The index of a prime p is the k with p = prime(k), where prime(1) = 2 (the OEIS convention of
  A000040). It is `Nat.primeCounting p`, the number of primes <= p.
* A prime with a palindromic prime index is a prime p whose index is itself a palindromic prime.
* "The only ... are 3, 5 and 11" is stated as a set equality: these three primes have the property
  (3 = prime(2), 5 = prime(3), 11 = prime(5)) and no other prime has it.
-/

namespace OMA.S_oeis_a002385

/-- `n` is a palindromic prime: a prime whose decimal expansion is a palindrome. -/
def IsPalindromicPrime (n : ℕ) : Prop :=
  n.Prime ∧ (Nat.digits 10 n).Palindrome

/-- Ianakiev's conjecture on A002385: the palindromic primes whose index is a palindromic prime
are exactly 3, 5 and 11. -/
theorem main :
    {p : ℕ | IsPalindromicPrime p ∧ IsPalindromicPrime (Nat.primeCounting p)} = {3, 5, 11} := by
  sorry

end OMA.S_oeis_a002385
