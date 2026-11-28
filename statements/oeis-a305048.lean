import Mathlib

/-!
# A305048: every prime p > 7 has a primitive root below p of the form 5^k + 10^m

Source: https://oeis.org/A305048

A305048 (offset 1): `a(n)` is the number of ordered pairs `(k, m)` of nonnegative integers such
that `5^k + 10^m` is not only a primitive root modulo `prime(n)` but also smaller than
`prime(n)`: 0, 1, 1, 0, 2, 3, 2, 2, 2, 4, …  For example `a(14) = 1` with `5^2 + 10^0 = 26` a
primitive root modulo `prime(14) = 43`.

Conjecture (Zhi-Wei Sun, May 24 2018): `a(n) > 0` for all `n > 4`. In other words, any prime
`p > 7` has a primitive root `g < p` of the form `5^k + 10^m` with `k` and `m` nonnegative
integers. The entry notes that this has been verified for every prime `7 < p ≤ 10^9`.

The conjecture is stated in the entry's own in-other-words form (`n > 4` is the same as
`prime(n) > 7`, since `prime(4) = 7`).

Conventions:
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- `k` and `m` range over `ℕ`, so the exponents may be `0`.
-/

namespace OMA.S_oeis_a305048

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 7 < p →
      ∃ k m : ℕ, 5 ^ k + 10 ^ m < p ∧ IsPrimitiveRootMod (5 ^ k + 10 ^ m) p := by
  sorry

end OMA.S_oeis_a305048
