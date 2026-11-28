import Mathlib

/-!
# A236308: a prime q < p/2 whose Catalan number C(q) is a primitive root modulo p

Source: https://oeis.org/A236308

A236308 (offset 1): `a(n)` is the number of primes `q < prime(n)/2` such that the Catalan number
`C(q)` is a primitive root modulo `prime(n)`. For example `a(13) = 1` since `C(7) = 429` is a
primitive root modulo `prime(13) = 41`.

Conjecture (Zhi-Wei Sun, Apr 21 2014): `a(n) > 0` for all `n > 2`. In other words, for any prime
`p > 3`, there exists a prime `q < p/2` such that the Catalan number
`C(q) = binomial(2q, q)/(q+1)` is a primitive root modulo `p`. The entry notes that this has been
verified for all `n = 3, …, 2*10^5`.

The conjecture is stated in the entry's own in-other-words form (`n > 2` is the same as
`prime(n) > 3`, since `prime(2) = 3`).

Conventions:
- `C(q)` is Mathlib's `catalan q`, the `q`-th Catalan number `binomial(2q, q)/(q+1)`.
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- The real inequality `q < p/2` is written as `2*q < p`.
-/

namespace OMA.S_oeis_a236308

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

theorem main :
    ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∃ q : ℕ, Nat.Prime q ∧ 2 * q < p ∧ IsPrimitiveRootMod (catalan q) p := by
  sorry

end OMA.S_oeis_a236308
