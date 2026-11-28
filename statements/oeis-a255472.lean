import Mathlib

/-!
# A255472: Number of decompositions of 2n into sums of two primes p <= q such that one or both p and q are elements of A023201.

Source: https://oeis.org/A255472
Credit: @eltociear

A023201 lists the primes `p` such that `p + 6` is also prime (`5, 7, 11, 13, 17, 23, ...`).
`a(n)` (offset 1) counts the ways to write `2n = p + q` with primes `p ≤ q` such that at least one
of `p`, `q` is in A023201. The entry conjectures:

  for all n > 3, a(n) > 0.

`main` states that a decomposition exists for every `n > 3`. As `p` and `q` are already required
to be prime, membership of `p` in A023201 reduces to `p + 6` being prime.
-/

namespace OMA.S_oeis_a255472

/-- Membership in OEIS A023201: `p` and `p + 6` are both prime. -/
def IsA023201 (p : ℕ) : Prop := p.Prime ∧ (p + 6).Prime

/-- The conjecture in OEIS A255472: for every `n > 3`, `2n = p + q` with primes `p ≤ q`, at least
one of which is in A023201. -/
theorem main : ∀ n : ℕ, 3 < n →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ q ∧ p + q = 2 * n ∧ (IsA023201 p ∨ IsA023201 q) := by
  sorry

end OMA.S_oeis_a255472
-- ci: re-run check-proof
