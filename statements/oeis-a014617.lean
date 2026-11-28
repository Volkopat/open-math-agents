import Mathlib

/-!
# A014617: First Borve Conjecture (zero-only antidiagonals of the prime-composite array)

Source: https://oeis.org/A014617
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (First Borve Conjecture):
Let `c(m)` be the `m`-th composite number and `p(n)` be the `n`-th prime.
The prime-composite array `B(m, n)` is the highest power of `p(n)` dividing `c(m)`.
The `m`-th antidiagonal consists of `B(m, 1), B(m - 1, 2), ..., B(1, m)`.
There are infinitely many `m ≥ 1` whose `m`-th antidiagonal consists entirely of zeros.

Conventions:
- `IsComposite x` holds iff `x ≥ 4 ∧ ¬ Nat.Prime x`.
- Using 0-indexed `Nat.nth`, `B(m - k, k + 1) = 0` iff
  `¬ (Nat.nth Nat.Prime k ∣ Nat.nth IsComposite (m - 1 - k))`.
-/

namespace OMA.S_oeis_a014617

def IsComposite (x : ℕ) : Prop :=
  x ≥ 4 ∧ ¬ Nat.Prime x

theorem main :
    Set.Infinite
      {m : ℕ | m ≥ 1 ∧ ∀ k : ℕ, k < m →
        ¬ (Nat.nth Nat.Prime k ∣ Nat.nth IsComposite (m - 1 - k))} := by
  sorry

end OMA.S_oeis_a014617
