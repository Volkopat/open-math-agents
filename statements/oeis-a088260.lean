import Mathlib

/-!
# A088260: Primorials which yield palindromes if the trailing zeros are deleted.

Source: https://oeis.org/A088260
Credit: @keiichisince1986-bot

A088260 lists the primorials that become palindromes (in decimal) once their trailing zeros are
deleted: `1, 2, 6, 30, 30030, 9699690`.
The entry states: Conjecture: sequence is finite. (Next term, if it exists, is `> 10^100000`.)

Conventions:
- The primorials are the values of Mathlib's `primorial n` (the product of the primes `≤ n`):
  `1, 2, 6, 30, 210, 2310, 30030, …` (A002110).
- `Nat.digits 10 m` lists the decimal digits of `m` from the least significant one, so dropping
  its leading `0` entries deletes the trailing zeros of `m`. The result is a palindrome when the
  remaining list equals its reverse.
- The conjecture says that the set of such primorials is finite.
-/

namespace OMA.S_oeis_a088260

/-- `m` is a palindrome in base 10 once its trailing zeros are deleted. -/
def IsPalindromeWithoutTrailingZeros (m : ℕ) : Prop :=
  ((Nat.digits 10 m).dropWhile (· = 0)).reverse = (Nat.digits 10 m).dropWhile (· = 0)

theorem main :
    {m : ℕ | (∃ n : ℕ, m = primorial n) ∧ IsPalindromeWithoutTrailingZeros m}.Finite := by
  sorry

end OMA.S_oeis_a088260
