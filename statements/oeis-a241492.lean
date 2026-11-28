import Mathlib

/-!
# A241492: every prime p > 7 has a primitive root below p of the form k*(k+1)

Source: https://oeis.org/A241492

A241492 (offset 1): `a(n) = |{0 < g < prime(n) : g is a primitive root modulo prime(n) and g is
a product of two consecutive integers}|`. For example `a(9) = 1` since `4*5 = 20` is a primitive
root modulo `prime(9) = 23`.

Conjecture (Zhi-Wei Sun, Apr 23 2014): `a(n) > 0` for all `n > 4`. In other words, any prime
`p > 7` has a primitive root `g < p` of the form `k*(k+1)`. The entry notes that this has been
verified for all `n = 5, …, 2*10^5`.

The conjecture is stated in the entry's own in-other-words form (`n > 4` is the same as
`prime(n) > 7`, since `prime(4) = 7`).

Conventions:
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- `k` ranges over `ℕ`. The value `k = 0` gives `g = 0`, which is not a primitive root, so the
  condition `0 < g` of the sequence definition holds automatically.
-/

namespace OMA.S_oeis_a241492

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 7 < p →
      ∃ k : ℕ, k * (k + 1) < p ∧ IsPrimitiveRootMod (k * (k + 1)) p := by
  sorry

end OMA.S_oeis_a241492
