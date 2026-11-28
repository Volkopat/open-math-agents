import Mathlib

/-!
# A254041: Number of decompositions of 2n into an unordered sum of two sexy primes.

Source: https://oeis.org/A254041
Credit: @eltociear

The "sexy primes" of this entry are the terms of A136207: primes `p` such that `p - 6` or `p + 6`
is prime (`5, 7, 11, 13, 17, 19, 23, ...`). `a(n)` (offset 1) counts the ways to write `2n` as an
unordered sum of two such primes. The entry conjectures:

  a(n) > 0 for n > 4.

`main` states that for every `n > 4`, `2n` is the sum of two (not necessarily distinct) terms of
A136207. In `IsA136207`, `p - 6` is natural subtraction: for `p ≤ 6` it is `0`, which is not
prime, so the truncation adds nothing.
-/

namespace OMA.S_oeis_a254041

/-- Membership in OEIS A136207: `p` is prime and `p - 6` or `p + 6` is prime. -/
def IsA136207 (p : ℕ) : Prop := p.Prime ∧ ((p - 6).Prime ∨ (p + 6).Prime)

/-- The conjecture in OEIS A254041: for every `n > 4`, `2n` is a sum of two sexy primes. -/
theorem main : ∀ n : ℕ, 4 < n → ∃ p q : ℕ, IsA136207 p ∧ IsA136207 q ∧ p + q = 2 * n := by
  sorry

end OMA.S_oeis_a254041
-- ci: re-run check-proof
