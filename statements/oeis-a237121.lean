import Mathlib

/-!
# A237121: a prime q < p/2 with the partition number P(q) a primitive root modulo p

Source: https://oeis.org/A237121

A237121 (offset 1): `a(n)` is the number of primes `p < prime(n)/2` such that `P(p)` is a
primitive root modulo `prime(n)`, where `P(.)` is the partition function A000041. For example
`a(14) = 1` since 3 is a prime smaller than `prime(14)/2 = 43/2` and `P(3) = 3` is a primitive
root modulo `prime(14) = 43`.

Conjecture (Zhi-Wei Sun, Apr 22 2014): `a(n) > 0` for all `n > 2`. In other words, for any prime
`p > 3`, there is a prime `q < p/2` with `P(q) = A000041(q)` a primitive root modulo `p`.

The conjecture is stated in the entry's own in-other-words form (`n > 2` is the same as
`prime(n) > 3`, since `prime(2) = 3`).

Conventions:
- `P(q)` is the number of partitions of `q`, the cardinality of Mathlib's type `Nat.Partition q`
  (1, 1, 2, 3, 5, 7, 11, 15, … for `q = 0, 1, 2, …`).
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- The real inequality `q < p/2` is written as `2*q < p`.
-/

namespace OMA.S_oeis_a237121

/-- The partition function A000041: the number of partitions of `n`. -/
def partitionNumber (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∃ q : ℕ, Nat.Prime q ∧ 2 * q < p ∧ IsPrimitiveRootMod (partitionNumber q) p := by
  sorry

end OMA.S_oeis_a237121
