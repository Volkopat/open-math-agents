import Mathlib

/-!
# A242345: a prime q < p with both q and 2^q - q primitive roots modulo p

Source: https://oeis.org/A242345

A242345 (offset 1): `a(n)` is the number of primes `p < prime(n)` with `p` and `2^p - p` both
primitive roots modulo `prime(n)`. For example `a(4) = 1` since 3 is a prime smaller than
`prime(4) = 7`, and both `3` and `2^3 - 3 = 5` are primitive roots modulo 7.

Conjecture (Zhi-Wei Sun, May 11 2014): `a(n) > 0` for all `n > 1`. In other words, for any odd
prime `p`, there is a prime `q < p` such that both `q` and `2^q - q` are primitive roots modulo
`p`.

The conjecture is stated in the entry's own in-other-words form (`n > 1` is the same as
`prime(n)` being an odd prime).

Conventions:
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- The odd primes are the primes `p` with `2 < p`. The subtraction `2^q - q` is exact in `ℕ`
  because `q < 2^q`.
-/

namespace OMA.S_oeis_a242345

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 2 < p →
      ∃ q : ℕ, Nat.Prime q ∧ q < p ∧ IsPrimitiveRootMod q p ∧
        IsPrimitiveRootMod (2 ^ q - q) p := by
  sorry

end OMA.S_oeis_a242345
