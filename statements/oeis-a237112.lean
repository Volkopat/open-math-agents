import Mathlib

/-!
# A237112: a prime q < p/2 with q! a primitive root modulo p

Source: https://oeis.org/A237112

A237112 (offset 1): `a(n)` is the number of primes `p < prime(n)/2` with `p!` a primitive root
modulo `prime(n)`. For example `a(7) = 1` since 3 is a prime smaller than `prime(7)/2 = 17/2`
and `3! = 6` is a primitive root modulo `prime(7) = 17`.

Conjecture (Zhi-Wei Sun, Apr 22 2014): `a(n) > 0` for all `n > 4`. In other words, for any prime
`p > 7`, there exists a prime `q < p/2` such that `q!` is a primitive root modulo `p`.

The conjecture is stated in the entry's own in-other-words form (`n > 4` is the same as
`prime(n) > 7`, since `prime(4) = 7`).

Conventions:
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- The real inequality `q < p/2` is written as `2*q < p`.
-/

namespace OMA.S_oeis_a237112

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 7 < p →
      ∃ q : ℕ, Nat.Prime q ∧ 2 * q < p ∧ IsPrimitiveRootMod q.factorial p := by
  sorry

end OMA.S_oeis_a237112
