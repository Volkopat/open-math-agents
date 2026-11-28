import Mathlib

/-!
# OEIS A190898

Source: https://oeis.org/A190898
Credit: @itsrainingmani

A190898(n) is the least odd prime p > n^2 for which the Legendre symbol
(n/p) equals 1. Zhi-Wei Sun conjectures that A190898(n) < (n+1)^2
for every positive integer n.

We state the equivalent existence formulation: the least qualifying prime
is below the upper bound exactly when some qualifying prime is below it.
The inequalities are strict, and oddness is explicit, including at n = 1.
Mathlib writes the Legendre symbol with the prime as its first argument.
-/

namespace OMA.S_oeis_a190898

/-- Between consecutive positive squares there is an odd prime for which
n is a nonzero quadratic residue. -/
theorem main : ∀ n : ℕ, 0 < n →
    ∃ (p : ℕ) (hp : p.Prime), Odd p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 ∧
      @legendreSym p ⟨hp⟩ (n : ℤ) = 1 := by
  sorry

end OMA.S_oeis_a190898
