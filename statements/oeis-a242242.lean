import Mathlib

/-!
# OEIS A242242: a primitive root g with 2^g - 1 also a primitive root

Source: https://oeis.org/A242242
Conjecture: Zhi-Wei Sun.
Credit: @biondadave

A242242(n) is the least positive primitive root `g < prime(n)` modulo `prime(n)` with `2^g - 1`
also a primitive root modulo `prime(n)`, or `0` if such a number `g` does not exist.

Conjecture: `a(n) > 0` except for `n = 2`. In other words, for any prime `p > 3`, there exists a
primitive root `0 < g < p` modulo `p` such that `2^g - 1` is also a primitive root modulo `p`.

Formalization notes:
* An integer `x` is a primitive root modulo `p` when its residue has multiplicative order
  `p - 1`: `IsPrimitiveRoot (x : ZMod p) (p - 1)`.
* The statement follows the conjecture and the definition, not the listed data: the entry's
  Mathematica program has a typo (`rMod` for `Mod`) that disables the test that `2^g - 1` is a
  primitive root, so some listed terms are too small (e.g. `a(5) = 2`, although `2^2 - 1 = 3`
  has order 5 modulo 11; the correct least value is 6). With the condition as defined, a
  suitable `g` exists for every prime `5 ≤ p < 300000` (checked numerically).
-/

namespace OMA.S_oeis_a242242

/-- For every prime `p > 3` there is a primitive root `0 < g < p` modulo `p` such that
`2^g - 1` is also a primitive root modulo `p`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 3 < p → ∃ g : ℕ, 0 < g ∧ g < p ∧
      IsPrimitiveRoot (g : ZMod p) (p - 1) ∧
      IsPrimitiveRoot ((2 ^ g - 1 : ℕ) : ZMod p) (p - 1) := by
  sorry

end OMA.S_oeis_a242242
