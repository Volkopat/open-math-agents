import Mathlib

/-!
# A291615: a prime q < p that is a primitive root modulo p and modulo prime(q)

Source: https://oeis.org/A291615

A291615 (offset 1): `a(n)` is the number of primes `p < prime(n)` such that `p` is a primitive
root modulo `prime(n)` and also a primitive root modulo `prime(p)`: 0, 1, 2, 1, 2, 3, 3, 3, 2, …
For example `a(4) = 1` since the prime `3 < prime(4) = 7` is a primitive root modulo 7 and also a
primitive root modulo `prime(3) = 5`.

Conjecture (Zhi-Wei Sun, Aug 27 2017): `a(n) > 0` for all `n > 1`. In other words, for any odd
prime `p` there is a prime `q < p` such that `q` is a primitive root modulo `p` and also a
primitive root modulo `prime(q)`.

The conjecture is stated in the entry's own in-other-words form.

Conventions:
- `prime(q)` is the `q`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (q - 1)`.
- An integer `g` is a primitive root modulo the prime `p` when its residue class generates the
  multiplicative group of `ZMod p`, i.e. has multiplicative order `p - 1`. This is written as
  `orderOf (g : ZMod p) = p - 1`; a multiple of `p` has `orderOf` equal to `0` and so is never a
  primitive root.
- The odd primes are the primes `p` with `2 < p`.
-/

namespace OMA.S_oeis_a291615

/-- `g` is a primitive root modulo `p`: its class in `ZMod p` has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (g p : ℕ) : Prop := orderOf (g : ZMod p) = p - 1

/-- The `k`-th prime, with `nthPrime 1 = 2`. -/
noncomputable def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

theorem main :
    ∀ p : ℕ, Nat.Prime p → 2 < p →
      ∃ q : ℕ, Nat.Prime q ∧ q < p ∧ IsPrimitiveRootMod q p ∧
        IsPrimitiveRootMod q (nthPrime q) := by
  sorry

end OMA.S_oeis_a291615
