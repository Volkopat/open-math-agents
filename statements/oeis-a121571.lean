import Mathlib

/-!
# OEIS A121571: sums of fourth powers of distinct primes

Source: https://oeis.org/A121571
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the largest number that is not a sum of `n`-th powers of distinct primes. Conjecture
(Noe): `a(4) = 340250525752`, and exactly `31332338304` positive numbers cannot be written as a
sum of fourth powers of distinct primes.

Conventions:
* A sum of fourth powers of distinct primes is `∑_{p ∈ s} p⁴` for a finite set `s` of primes
  (the empty sum `0` is excluded from 'positive numbers').
-/

namespace OMA.S_oeis_a121571

/-- `m` is a sum of fourth powers of distinct primes. -/
def Rep (m : ℕ) : Prop := ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime) ∧ m = ∑ p ∈ s, p ^ 4

/-- Noe's conjecture on fourth powers. -/
theorem main : ¬ Rep 340250525752 ∧ (∀ m : ℕ, 340250525752 < m → Rep m) ∧
    {m : ℕ | 0 < m ∧ ¬ Rep m}.ncard = 31332338304 := by
  sorry

end OMA.S_oeis_a121571
