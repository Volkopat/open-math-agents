import Mathlib

/-!
# OEIS A048161: primes `p` with `(p² + 1)/2` prime; infinitely many?

Source: https://oeis.org/A048161
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The entry conjectures that there are infinitely many such primes (equivalently, infinitely many
of the associated triangles). Statement: the set of primes `p` such that `(p² + 1)/2` is prime is
infinite. We require `p` odd so that `(p² + 1)/2` is an exact quotient (for `p = 2` it is
not an integer, and natural-number division would otherwise admit it spuriously).
-/

namespace OMA.S_oeis_a048161

/-- The conjecture. -/
theorem main : {p : ℕ | p.Prime ∧ Odd p ∧ ((p ^ 2 + 1) / 2).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a048161
