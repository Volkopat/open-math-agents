import Mathlib

/-!
# A236306: a prime q < p with both q and q! primitive roots modulo p

Source: https://oeis.org/A236306

A236306 (offset 1): `a(n)` is the least prime `p < prime(n)` for which both `p` and `p!` are
primitive roots modulo `prime(n)`, or 0 if such a prime does not exist. For example `a(7) = 3`
since both `3` and `3! = 6` are primitive roots modulo `prime(7) = 17`, but `2` is not.

Conjecture (Zhi-Wei Sun, Apr 21 2014): `a(n) > 0` for all `n > 4`. In other words, for any prime
`p > 7`, there exists a prime `q < p` such that both `q` and `q!` are primitive roots modulo `p`.

The conjecture is stated in the entry's own in-other-words form (`n > 4` is the same as
`prime(n) > 7`, since `prime(4) = 7`).

Conventions:
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
-/

namespace OMA.S_oeis_a236306

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 7 < p →
      ∃ q : ℕ, Nat.Prime q ∧ q < p ∧ IsPrimitiveRootMod q p ∧
        IsPrimitiveRootMod q.factorial p := by
  sorry

end OMA.S_oeis_a236306
