import Mathlib

/-!
# A239963: every prime p > 3 has a triangular primitive root below p

Source: https://oeis.org/A239963

A239963 (offset 1): `a(n)` is the number of triangular numbers below `prime(n)` which are also
primitive roots modulo `prime(n)`. For example `a(5) = 1` since the triangular number
`3*4/2 = 6` is a primitive root modulo `prime(5) = 11`.

Conjecture (Zhi-Wei Sun, Apr 23 2014): `a(n) > 0` for all `n > 2`. In other words, for any prime
`p > 3`, there is a primitive root `0 < g < p` of the form `k*(k+1)/2`, where `k` is a positive
integer.

The conjecture is stated in the entry's own in-other-words form (`n > 2` is the same as
`prime(n) > 3`, since `prime(2) = 3`).

Conventions:
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- `k*(k+1)/2` uses natural-number division, which is exact because `k*(k+1)` is even. Since
  `k > 0`, the condition `0 < g` holds automatically and only `g < p` is stated.
-/

namespace OMA.S_oeis_a239963

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∃ k : ℕ, 0 < k ∧ k * (k + 1) / 2 < p ∧ IsPrimitiveRootMod (k * (k + 1) / 2) p := by
  sorry

end OMA.S_oeis_a239963
