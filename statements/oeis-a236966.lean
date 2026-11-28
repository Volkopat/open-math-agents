import Mathlib

/-!
# A236966: a prime q < p/2 with the Mersenne number 2^q - 1 a primitive root modulo p

Source: https://oeis.org/A236966

A236966 (offset 1): `a(n)` is the number of primes `p < prime(n)/2` such that `2^p - 1` is a
primitive root modulo `prime(n)`. For example `a(12) = 1` since 17 is a prime smaller than
`prime(12)/2 = 37/2` with `2^17 - 1 = 131071` a primitive root modulo `prime(12) = 37`.

Conjecture (Zhi-Wei Sun, Apr 22 2014): `a(n) > 0` for all `n > 2`. In other words, for any prime
`p > 3`, there is a prime `q < p/2` with the Mersenne number `2^q - 1` a primitive root modulo
`p`. The entry notes that this has been verified for all `n = 3, …, 530000`.

The conjecture is stated in the entry's own in-other-words form (`n > 2` is the same as
`prime(n) > 3`, since `prime(2) = 3`).

Conventions:
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- The real inequality `q < p/2` is written as `2*q < p`; `2^q - 1` is an exact subtraction in
  `ℕ`.
-/

namespace OMA.S_oeis_a236966

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∃ q : ℕ, Nat.Prime q ∧ 2 * q < p ∧ IsPrimitiveRootMod (2 ^ q - 1) p := by
  sorry

end OMA.S_oeis_a236966
