import Mathlib

/-!
# A293659: Base-6 circular primes that are not base-6 repunits.

Source: https://oeis.org/A293659
Credit: @keiichisince1986-bot

A293659 lists, in increasing order and written in decimal, the base-6 circular primes that are
not base-6 repunits: `11, 31, 71, 191, 211`.
The entry states: Conjecture: The sequence is finite, with 211 being the last term (see A293142).

Conventions:
- A base-6 circular prime is a prime such that every number obtained by cyclically permuting its
  base-6 digits is prime (A293142). `IsCircularPrime n`: for every `k`, the number whose base-6
  digit list is the digit list of `n` rotated by `k` places is prime. Rotating by `0` gives `n`
  itself, so `n` is prime. `Nat.digits 6` lists the digits from the least significant one; the
  set of all rotations of a cyclic word does not depend on that direction.
- A rotation that brings a digit `0` to the leading position is read with the usual
  `Nat.ofDigits` convention. This choice never matters: if a number with at least two digits
  contains a `0`, the rotation that makes `0` the last digit is a positive multiple of `6`, which
  is not prime.
- The OEIS data, and the PARI program of the entry, exclude every number whose base-6 digits
  are all equal (`vecmin(digits(p, 6)) != vecmax(digits(p, 6))`): this removes the base-6
  repunits and also the one-digit primes. Among primes, the numbers with all base-6 digits equal
  are exactly the repunit primes with at least two digits and the primes below `6`, since a
  number `d · (11…1)` with `d ≥ 2` and at least two digits is composite. We follow the data:
  `HasEqualDigits n` excludes them. This changes the set only by finitely many one-digit numbers,
  so it does not affect the conjecture.
- The sequence is finite with last term `211` exactly when `211` is the greatest
  element of the set of terms: `IsGreatest S 211` says that `211 ∈ S` and every
  element of `S` is at most `211`, so `S` is finite.
-/

namespace OMA.S_oeis_a293659

/-- Every cyclic permutation of the base-6 digits of `n` is a prime. -/
def IsCircularPrime (n : ℕ) : Prop :=
  ∀ k : ℕ, (Nat.ofDigits 6 ((Nat.digits 6 n).rotate k)).Prime

/-- All base-6 digits of `n` are equal (true for `n = 0`, whose digit list is empty). -/
def HasEqualDigits (n : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 6 n, ∀ e ∈ Nat.digits 6 n, d = e

theorem main : IsGreatest {n : ℕ | IsCircularPrime n ∧ ¬ HasEqualDigits n} 211 := by
  sorry

end OMA.S_oeis_a293659
