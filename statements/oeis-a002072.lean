import Mathlib

/-!
# A002072: Upper Bound on the Largest Smooth Consecutive Pair

Source: https://oeis.org/A002072
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

For `n ≥ 1`, `A002072(n)` is the smallest natural number `m` such that for all `k > m`, either `k`
or `k + 1` has a prime factor strictly greater than the `n`-th prime `p_n`.

Conjecture: `A002072(n) < 10^n / n` for all `n ≥ 1` with `n ≠ 4`.
-/

namespace OMA.S_oeis_a002072

/-- The smallest `m` such that every `k > m` has a prime factor `> p_n` dividing `k` or `k + 1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf { m : ℕ | ∀ k > m, ∃ p : ℕ, Nat.Prime p ∧ Nat.nth Nat.Prime (n - 1) < p ∧
    (p ∣ k ∨ p ∣ k + 1) }

theorem main :
    ∀ n : ℕ, 1 ≤ n → n ≠ 4 → n * a n < 10 ^ n := by
  sorry

end OMA.S_oeis_a002072
