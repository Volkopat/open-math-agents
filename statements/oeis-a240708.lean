import Mathlib

/-!
# A240708: Number of decompositions of 2n into an unordered sum of two terms of A240699.

Source: https://oeis.org/A240708
Credit: @eltociear

A240699 lists the primes `p` such that at least one of `p ± 2`, `p ± 4`, `p ± 6` is also prime
(`3, 5, 7, 11, 13, ...`; `2` is not a term). `a(n)` (offset 1) is the number of ways to write `2n`
as an unordered sum of two terms of A240699. The entry conjectures:

  for `n ≥ 3`, this sequence is always positive,

a strengthening of the Goldbach conjecture. Positivity of `a(n)` means that `2n` is the sum of two
(not necessarily distinct) terms of A240699, and `main` states exactly that. The order of the two
summands does not matter for existence.

In `IsA240699`, `p - d` is natural subtraction, so it is guarded by `d < p`: the term `p - d` is
only considered when it is a positive integer. A prime cannot be `0`, so for `d ≥ p` there is
nothing to consider.
-/

namespace OMA.S_oeis_a240708

/-- Membership in OEIS A240699: `p` is prime and at least one of `p ± 2`, `p ± 4`, `p ± 6` is
prime. -/
def IsA240699 (p : ℕ) : Prop :=
  p.Prime ∧ ∃ d ∈ ({2, 4, 6} : Finset ℕ), (p + d).Prime ∨ (d < p ∧ (p - d).Prime)

/-- The conjecture in OEIS A240708: for every `n ≥ 3`, `2n` is a sum of two terms of A240699. -/
theorem main : ∀ n : ℕ, 3 ≤ n → ∃ p q : ℕ, IsA240699 p ∧ IsA240699 q ∧ p + q = 2 * n := by
  sorry

end OMA.S_oeis_a240708
-- ci: re-run check-proof
