import Mathlib

/-!
# OEIS A045917: two conjectures on Goldbach decompositions

Source: https://oeis.org/A045917
`a n` is the number of decompositions of `2n` into an unordered sum of two primes. Besides
the Goldbach conjecture, the entry records:
1. if `p` ranges over the primes occurring in decompositions of `2n`, then `n = 4` and `n = 6`
   are the only `n` such that `2n + p` is prime for every such `p`;
2. every `m ≥ 0` is a value of `a`: for every `m` there is `n` with `a n = m`.
`main` is the conjunction of 1 and 2.

Conventions. A prime "in a decomposition of `2n`" is a prime `p ≤ 2n` with `2n - p` prime.
In 1 we require `n ≥ 2` and at least one decomposition, so that the condition is not vacuous
(for `n = 4`, `8 = 3 + 5` and `11, 13` are prime; for `n = 6`, `12 = 5 + 7` and `17, 19`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a045917

/-- Unordered decompositions `2n = p + q`, `p ≤ q` primes. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun p => p.Prime ∧ (2 * n - p).Prime).card

/-- `p` occurs in a decomposition of `2n` into two primes. -/
def InDecomp (n p : ℕ) : Prop := p ≤ 2 * n ∧ p.Prime ∧ (2 * n - p).Prime

theorem main :
    (∀ n : ℕ, 2 ≤ n → (∃ p, InDecomp n p) →
        ((∀ p, InDecomp n p → (2 * n + p).Prime) ↔ n = 4 ∨ n = 6)) ∧
    (∀ m : ℕ, ∃ n : ℕ, a n = m) := by
  sorry

end OMA.S_oeis_a045917
