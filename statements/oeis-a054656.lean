import Mathlib

/-!
# OEIS A054656: primes missing from all partitions of `n` into distinct primes

Source: https://oeis.org/A054656
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of primes `p ≤ n` that do not appear in any partition of `n` into distinct
primes. Conjecture (OEIS entry): for `n ≥ 23`, `a(n) = 2` if both `n - 6` and `n - 4` are prime,
`a(n) = 1` if one of `n - 6`, `n - 4`, `n - 1` is prime, and `a(n) = 0` otherwise.

Conventions:
* A partition of `n` into distinct primes is a finite set of primes with sum `n`. The three cases
  are read in order (the first applies when both `n - 6` and `n - 4` are prime).
-/

namespace OMA.S_oeis_a054656

/-- `p` appears in some partition of `n` into distinct primes. -/
def Appears (n p : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ q ∈ s, q.Prime) ∧ p ∈ s ∧ ∑ q ∈ s, q = n

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := {p : ℕ | p.Prime ∧ p ≤ n ∧ ¬ Appears n p}.ncard

/-- The conjectured classification for `n ≥ 23`. -/
theorem main : ∀ n : ℕ, 23 ≤ n →
    a n = if (n - 6).Prime ∧ (n - 4).Prime then 2
      else if (n - 6).Prime ∨ (n - 4).Prime ∨ (n - 1).Prime then 1 else 0 := by
  sorry

end OMA.S_oeis_a054656
