import Mathlib

/-!
# A293661: Base-8 circular primes that are not base-8 repunits.

Source: https://oeis.org/A293661
Credit: @keiichisince1986-bot

A293661 lists, in increasing order and written in decimal, the base-8 circular primes that are
not base-8 repunits: `13, 29, 31, 41, 43, 47, 59, 61, 607, 719, 751, 761, 971, 1021, …`.
The entry states: Conjecture: The sequence is finite.

Conventions:
- A base-8 circular prime is a prime such that every number obtained by cyclically permuting its
  base-8 digits is prime (A293142). `IsCircularPrime n`: for every `k`, the number whose base-8
  digit list is the digit list of `n` rotated by `k` places is prime. Rotating by `0` gives `n`
  itself, so `n` is prime. `Nat.digits 8` lists the digits from the least significant one; the
  set of all rotations of a cyclic word does not depend on that direction.
- A rotation that brings a digit `0` to the leading position is read with the usual
  `Nat.ofDigits` convention. This choice never matters: if a number with at least two digits
  contains a `0`, the rotation that makes `0` the last digit is a positive multiple of `8`, which
  is not prime.
- The OEIS data, and the PARI program of the entry, exclude every number whose base-8 digits
  are all equal (`vecmin(digits(p, 8)) != vecmax(digits(p, 8))`): this removes the base-8
  repunits and also the one-digit primes. Among primes, the numbers with all base-8 digits equal
  are exactly the repunit primes with at least two digits and the primes below `8`, since a
  number `d · (11…1)` with `d ≥ 2` and at least two digits is composite. We follow the data:
  `HasEqualDigits n` excludes them. This changes the set only by finitely many one-digit numbers,
  so it does not affect the conjecture.
- The conjecture says that the set of terms is finite.
-/

namespace OMA.S_oeis_a293661

/-- Every cyclic permutation of the base-8 digits of `n` is a prime. -/
def IsCircularPrime (n : ℕ) : Prop :=
  ∀ k : ℕ, (Nat.ofDigits 8 ((Nat.digits 8 n).rotate k)).Prime

/-- All base-8 digits of `n` are equal (true for `n = 0`, whose digit list is empty). -/
def HasEqualDigits (n : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 8 n, ∀ e ∈ Nat.digits 8 n, d = e

theorem main : {n : ℕ | IsCircularPrime n ∧ ¬ HasEqualDigits n}.Finite := by
  sorry

end OMA.S_oeis_a293661
