import Mathlib

/-!
# A237594: a prime q < p/2 with the Bell number B(q) a primitive root modulo p

Source: https://oeis.org/A237594

A237594 (offset 1): `a(n)` is the number of primes `p < prime(n)/2` such that the Bell number
`B(p)` is a primitive root modulo `prime(n)`. For example `a(9) = 1` since 3 is a prime smaller
than `prime(9)/2 = 23/2` and `B(3) = 5` is a primitive root modulo `prime(9) = 23`.

Conjecture (Zhi-Wei Sun, Apr 22 2014): `a(n) > 0` for all `n > 2`. In other words, for any prime
`p > 3`, there exists a prime `q < p/2` such that the Bell number `B(q)` is a primitive root
modulo `p`.

The conjecture is stated in the entry's own in-other-words form (`n > 2` is the same as
`prime(n) > 3`, since `prime(2) = 3`).

Conventions:
- `B(q)` is the `q`-th Bell number, the number of partitions of a set with `q` elements
  (1, 1, 2, 5, 15, 52, 203, … for `q = 0, 1, 2, …`), Mathlib's `Nat.bell q`.
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- The real inequality `q < p/2` is written as `2*q < p`.
-/

namespace OMA.S_oeis_a237594

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∃ q : ℕ, Nat.Prime q ∧ 2 * q < p ∧ IsPrimitiveRootMod (Nat.bell q) p := by
  sorry

end OMA.S_oeis_a237594
