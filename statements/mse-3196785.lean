import Mathlib

/-!
# Digit Sum of a Prime Power Equal to a Smaller Power of the Same Prime

Source: https://math.stackexchange.com/questions/3196785/are-there-infinitely-many-solutions-such-that-the-digit-sum-of-a-prime-power-is
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Denote by `s(m)` the base-10 digit sum of a natural number `m`.
Are there infinitely many triples `(p, n, k)` where `p` is prime and `n, k` are
positive integers with `k < n` such that `s(p^n) = p^k`?

## Formalization Notes
`Nat.digits 10 m` returns the list of base-10 digits of `m`, so its `.sum` is `s(m)`.
We include `k < n` matching the title ('a smaller power of the same prime'), noting
that `s(p^n) < p^n` already forces `k < n` for all `p^n ≥ 10`.
-/

namespace OMA.S_mse_3196785

theorem main :
    {t : ℕ × ℕ × ℕ |
      t.1.Prime ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.2.2 < t.2.1 ∧
      (Nat.digits 10 (t.1 ^ t.2.1)).sum = t.1 ^ t.2.2}.Infinite := by
  sorry

end OMA.S_mse_3196785
