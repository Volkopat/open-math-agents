import Mathlib

/-!
# A242248: a primitive root g < p with 2^g - 1 and (g-1)! also primitive roots modulo p

Source: https://oeis.org/A242248

A242248 (offset 1): `a(n) = |{0 < g < prime(n) : g, 2^g - 1 and (g-1)! are all primitive roots
modulo prime(n)}|`. For example `a(4) = 1` since `5`, `2^5 - 1 = 31` and `(5-1)! = 24` are all
primitive roots modulo `prime(4) = 7`.

Conjecture (Zhi-Wei Sun, May 09 2014): `a(n) > 0` for all `n > 2`. In other words, for any prime
`p > 3`, there exists a positive primitive root `g < p` modulo `p` such that `2^g - 1` and
`(g-1)!` are also primitive roots modulo `p`. The entry notes that this has been verified for
all primes `p` with `3 < p < 10^6`.

The conjecture is stated in the entry's own in-other-words form (`n > 2` is the same as
`prime(n) > 3`, since `prime(2) = 3`).

Conventions:
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- Everything is in `ℕ`; `2^g - 1` and `g - 1` are exact subtractions because `g > 0`.
-/

namespace OMA.S_oeis_a242248

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∃ g : ℕ, 0 < g ∧ g < p ∧ IsPrimitiveRootMod g p ∧ IsPrimitiveRootMod (2 ^ g - 1) p ∧
        IsPrimitiveRootMod (g - 1).factorial p := by
  sorry

end OMA.S_oeis_a242248
