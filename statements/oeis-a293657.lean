import Mathlib

/-!
# A293657: Base-4 circular primes that are not base-4 repunits.

Source: https://oeis.org/A293657
Credit: @keiichisince1986-bot

A293657 lists, in increasing order and written in decimal, the base-4 circular primes that are
not base-4 repunits: `7, 13, 23, 29, 53, 383, 509, 863, 983, 1013`.
The entry states: Conjecture: The sequence is finite, with 1013 being the last term (see A293142).

Conventions:
- A base-4 circular prime is a prime such that every number obtained by cyclically permuting its
  base-4 digits is prime (A293142). `IsCircularPrime n`: for every `k`, the number whose base-4
  digit list is the digit list of `n` rotated by `k` places is prime. Rotating by `0` gives `n`
  itself, so `n` is prime. `Nat.digits 4` lists the digits from the least significant one; the
  set of all rotations of a cyclic word does not depend on that direction.
- A rotation that brings a digit `0` to the leading position is read with the usual
  `Nat.ofDigits` convention. This choice never matters: if a number with at least two digits
  contains a `0`, the rotation that makes `0` the last digit is a positive multiple of `4`, which
  is not prime.
- The OEIS data, and the PARI program of the entry, exclude every number whose base-4 digits
  are all equal (`vecmin(digits(p, 4)) != vecmax(digits(p, 4))`): this removes the base-4
  repunits and also the one-digit primes. Among primes, the numbers with all base-4 digits equal
  are exactly the repunit primes with at least two digits and the primes below `4`, since a
  number `d · (11…1)` with `d ≥ 2` and at least two digits is composite. We follow the data:
  `HasEqualDigits n` excludes them. This changes the set only by finitely many one-digit numbers,
  so it does not affect the conjecture.
- The sequence is finite with last term `1013` exactly when `1013` is the greatest
  element of the set of terms: `IsGreatest S 1013` says that `1013 ∈ S` and every
  element of `S` is at most `1013`, so `S` is finite.
-/

namespace OMA.S_oeis_a293657

/-- Every cyclic permutation of the base-4 digits of `n` is a prime. -/
def IsCircularPrime (n : ℕ) : Prop :=
  ∀ k : ℕ, (Nat.ofDigits 4 ((Nat.digits 4 n).rotate k)).Prime

/-- All base-4 digits of `n` are equal (true for `n = 0`, whose digit list is empty). -/
def HasEqualDigits (n : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 4 n, ∀ e ∈ Nat.digits 4 n, d = e

theorem main : IsGreatest {n : ℕ | IsCircularPrime n ∧ ¬ HasEqualDigits n} 1013 := by
  sorry

end OMA.S_oeis_a293657
