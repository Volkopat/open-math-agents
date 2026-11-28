import Mathlib

/-!
# A023048: Existence of a prime having least positive primitive root n

Source: https://oeis.org/A023048
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Let `A023048(n)` be the smallest prime `p` whose least positive primitive root is `n`, or `0`
if no such prime exists.

Conjecture (from generalized Artin's conjecture): For every integer `n ≥ 2`, there exists a
prime `p` whose least positive primitive root is `n` if and only if `n` is not a perfect
power (i.e., `n` is not of the form `a^k` with `k ≥ 2`).
-/

namespace OMA.S_oeis_a023048

/-- `n` is a perfect power: `n = a^k` for some `a : ℕ` and `k ≥ 2`. -/
def isPerfectPower (n : ℕ) : Prop :=
  ∃ a k : ℕ, 2 ≤ k ∧ a ^ k = n

/-- `p` is a prime whose least positive primitive root is `n`. -/
def hasLeastPrimRoot (p n : ℕ) : Prop :=
  Nat.Prime p ∧
    orderOf (n : ZMod p) = p - 1 ∧
    ∀ m : ℕ, 1 ≤ m → m < n → orderOf (m : ZMod p) ≠ p - 1

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ((∃ p : ℕ, hasLeastPrimRoot p n) ↔ ¬ isPerfectPower n) := by
  sorry

end OMA.S_oeis_a023048
