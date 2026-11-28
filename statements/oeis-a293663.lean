import Mathlib

/-!
# A293663: Circular primes that are not repunits.

Source: https://oeis.org/A293663
Credit: @keiichisince1986-bot

A293663 is the relative complement of A004022 (repunit primes) in A068652 (numbers such that
every cyclic permutation of the decimal digits is a prime, i.e. circular primes):
`2, 3, 5, 7, 13, 17, 31, 37, 71, 73, 79, 97, 113, 131, 197, 199, 311, 337, 373, 719, 733, …`
The entry states: Conjecture: The sequence is finite.
(It has 54 terms below `10^6`, the largest being `999331`, and no further term below `10^23`.)

Conventions:
- `IsCircularPrime n`: for every `k`, the number whose decimal digit list is the digit list of
  `n` rotated by `k` places is prime. Rotating by `0` gives `n` itself, so `n` is prime; rotating
  by every `k` covers every cyclic permutation of the digits. `Nat.digits 10` lists the digits
  from the least significant one; the set of all rotations of a cyclic word does not depend on
  that direction.
- A rotation that brings a digit `0` to the leading position is read with the usual
  `Nat.ofDigits` convention (as a number with fewer digits). This choice never matters: if a
  number with at least two digits contains a `0`, the rotation that makes `0` the last digit is
  a positive multiple of `10`, which is not prime.
- `IsRepunit n`: `n` is positive and all its decimal digits are `1`
  (`1, 11, 111, …`), as in A002275; A004022 consists of the primes among these.
- The conjecture says that the set of circular primes that are not repunits is finite.
-/

namespace OMA.S_oeis_a293663

/-- Every cyclic permutation of the decimal digits of `n` is a prime. -/
def IsCircularPrime (n : ℕ) : Prop :=
  ∀ k : ℕ, (Nat.ofDigits 10 ((Nat.digits 10 n).rotate k)).Prime

/-- `n` is a repunit: positive, with every decimal digit equal to `1`. -/
def IsRepunit (n : ℕ) : Prop :=
  0 < n ∧ ∀ d ∈ Nat.digits 10 n, d = 1

theorem main : {n : ℕ | IsCircularPrime n ∧ ¬ IsRepunit n}.Finite := by
  sorry

end OMA.S_oeis_a293663
