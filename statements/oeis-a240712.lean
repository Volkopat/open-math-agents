import Mathlib

/-!
# A240712: number of unordered Goldbach-type decompositions of `2n` into terms of A240710.

Source: https://oeis.org/A240712 (and A240710)
Credit: @cjchaffin

A240710 is the primes `p` such that at least one of `p ± 6` and `p ± 12` is also prime
(so 2 and 3 are excluded, and 523 is the first prime after 3 that is excluded).

Conjecture (on the OEIS page): `a(n) > 0` for all `n > 4`. This is a stronger form of
Goldbach: every even integer `> 8` is a sum of two (not necessarily distinct) terms of
A240710. Formalized as existence, not the counting function.

Conventions: offset 1; unordered sums are written `p ≤ q` with `p + q = 2n`; natural
subtraction makes `p - 6` and `p - 12` fail to be prime automatically when `p` is too
small, matching the intended meaning.
-/

namespace OMA.S_oeis_a240712

/-- A prime `p` belongs to A240710 iff at least one of `p±6`, `p±12` is prime. -/
def IsA240710 (p : ℕ) : Prop :=
  p.Prime ∧ ((p + 6).Prime ∨ (p + 12).Prime ∨ (p - 6).Prime ∨ (p - 12).Prime)

theorem main : ∀ n : ℕ, 4 < n →
    ∃ p q : ℕ, IsA240710 p ∧ IsA240710 q ∧ p ≤ q ∧ p + q = 2 * n := by
  sorry

end OMA.S_oeis_a240712
